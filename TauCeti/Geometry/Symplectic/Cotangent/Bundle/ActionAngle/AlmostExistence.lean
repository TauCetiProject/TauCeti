/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.OutermostStratum
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Hamiltonian
public import TauCeti.Geometry.Symplectic.Hamiltonian.AlmostExistence

/-!
# No contractible almost existence for functions of the actions on `T*Tⁿ`

Let `p > 0`, let `Tⁿ = ι → AddCircle p` be the torus and `I = (I_j)` the actions of its cotangent
bundle `T*Tⁿ` (`TauCeti.CotangentBundle.torusActions`), with the canonical symplectic form
`ω = -dλ`. A Hamiltonian `H = h(I)` of the actions moves every point linearly on its invariant
torus, so a periodic orbit of `X_H` that is contractible in `T*Tⁿ` is constant
(`TauCeti.CotangentBundle.eq_of_isMIntegralCurve_hamiltonianVectorField_comp_torusActions`). A
closed characteristic is a nonconstant periodic orbit, so for `h` of class `C²` no level of `h ∘ I`
carries a closed characteristic contractible in any subset of `T*Tⁿ`
(`TauCeti.CotangentBundle.not_hasContractibleClosedCharacteristic_comp_torusActions`).

The action map is a submersion, so the regular values of `h ∘ I` are those of `h`
(`TauCeti.CotangentBundle.isRegularValue_comp_torusActions_iff`). By the Morse–Sard theorem almost
every value of `h` is regular when `h` is of class `Cᵏ` with `k ≥ #ι`. So for `k ≥ 2` as well,
no level of `h ∘ I` has the contractible almost existence property
(`TauCeti.CotangentBundle.not_hasContractibleAlmostExistence_comp_torusActions`), whatever its
value and whether or not it is regular. The regularity cannot be lowered below that of Sard's
theorem: if the critical values of `h` filled an interval, every level over that interval would be
critical, and the almost existence property, which only asks for closed characteristics on regular
levels, would hold there vacuously.

The case of interest is the kinetic energy `K = ½ ∑ⱼ I_j²` of the flat metric `∑ⱼ dθ_j²`
(`TauCeti.CotangentBundle.torusKineticEnergy`), whose level `K = 1/2` is the unit cosphere bundle
of the flat torus. It is smooth, its sublevel sets are compact
(`TauCeti.CotangentBundle.isCompact_preimage_Iic_torusKineticEnergy`), every nonzero value is
regular (`TauCeti.CotangentBundle.isRegularValue_torusKineticEnergy`), and it vanishes on the zero
section (`TauCeti.CotangentBundle.torusKineticEnergy_zeroSection`). So the regular level
`K⁻¹(1/2)` bounds the relatively compact domain `{K < 1/2}`, which contains the zero section, a
section of `T*Tⁿ → Tⁿ` and so of degree one over the torus. Yet it has no contractible almost
existence property
(`TauCeti.CotangentBundle.not_hasContractibleAlmostExistence_torusKineticEnergy`). The torus is
aspherical (`AddCircle.isAspherical_pi`), and this is why: the theorems of Barraud,
Damian, Humilière and Oancea that give almost existence near the zero section of `T*Q` assume
that `Q` is not aspherical, or that a higher homotopy group of `Q` is large, and those hypotheses
cannot be dropped.

## Main results

In the namespace `TauCeti.CotangentBundle`:

* `not_hasContractibleClosedCharacteristic_comp_torusActions`: no level of a `C²` function of the
  actions carries a contractible closed characteristic.
* `isRegularPoint_comp_torusActions_iff`, `isRegularValue_comp_torusActions_iff`: the regular
  points and values of a function of the actions are those of its profile.
* `not_hasContractibleAlmostExistence_comp_torusActions`: no level of a sufficiently smooth
  function of the actions has the contractible almost existence property.
* `not_hasContractibleAlmostExistence_torusKineticEnergy`: in particular no level of the flat
  kinetic energy has it, the unit cosphere bundle `K⁻¹(1/2)` included.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 1.1 and Theorems A and C.
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Section 4.2 (the almost existence theorem).
* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  Section 3 (the Morse–Sard theorem).
-/

public section

noncomputable section

open Bundle Function MeasureTheory Set
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Closed characteristics of functions of the actions -/

/-- **No level of a function of the actions carries a contractible closed characteristic.** For
`H = h(I)` with `h` of class `C²`, a periodic orbit of `X_H` whose loop is contractible in a subset
`W` of `T*Tⁿ`, hence in `T*Tⁿ`, is constant, while a closed characteristic is not. -/
theorem not_hasContractibleClosedCharacteristic_comp_torusActions {h : (ι → ℝ) → ℝ}
    (hh : ContDiff ℝ 2 h)
    (W : Set (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)))
    (c : ℝ) :
    ¬(symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle p)).HasContractibleClosedCharacteristic W (h ∘ torusActions p) c := by
  rw [SmoothTwoForm.hasContractibleClosedCharacteristic_iff]
  rintro ⟨T, γ, hT, hγ, hper, ⟨t, ht⟩, -, g, hg, hgγ⟩
  -- The loop is null-homotopic in `W`, hence in the whole cotangent bundle.
  exact ht (eq_of_isMIntegralCurve_hamiltonianVectorField_comp_torusActions p hh hγ hT hper
    ⟨(⟨Subtype.val, continuous_subtypeVal⟩ : C(W, _)).comp g, hg.comp_right _, hgγ⟩ t)

/-! ### Regular values of functions of the actions -/

/-- A function of the actions is regular at a covector exactly when its profile is regular at the
actions of the covector: the action map is a submersion. Where the profile is not differentiable
neither holds. -/
theorem isRegularPoint_comp_torusActions_iff {h : (ι → ℝ) → ℝ}
    {z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)} :
    IsRegularPoint ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ)
        (h ∘ torusActions p) z ↔
      Surjective (fderiv ℝ h (torusActions p z)) := by
  by_cases hh : DifferentiableAt ℝ h (torusActions p z)
  · rw [← isRegularPoint_iff_surjective_fderiv]
    exact ⟨fun hz ↦ hz.of_comp hh.mdifferentiableAt
        ((contMDiff_torusActions p z).mdifferentiableAt (by simp)),
      fun hz ↦ hz.comp (isRegularPoint_iff.2 (surjective_mfderiv_torusActions p z))⟩
  · refine iff_of_false
      (fun hz ↦ hh ((mdifferentiableAt_comp_torusActions_iff p).1 hz.mdifferentiableAt)) ?_
    rw [fderiv_zero_of_not_differentiableAt hh]
    intro h0
    obtain ⟨v, hv⟩ := h0 1
    simp at hv

/-- **The regular values of a function of the actions are those of its profile.** Every vector of
actions is the actions of some covector, so `c` is a regular value of `h ∘ I` exactly when the
derivative of `h` is surjective at every point of `h⁻¹(c)`. -/
theorem isRegularValue_comp_torusActions_iff {h : (ι → ℝ) → ℝ} {c : ℝ} :
    IsRegularValue ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ)
        (h ∘ torusActions p) c ↔
      ∀ a, h a = c → Surjective (fderiv ℝ h a) := by
  rw [isRegularValue_iff]
  refine ⟨fun hc a ha ↦ ?_,
    fun hc z hz ↦ (isRegularPoint_comp_torusActions_iff p).2 (hc _ hz)⟩
  -- The covector `κ(0, a)` has the actions `a`.
  have hz := hc (actionAngleCover p (0, a)) (by simp [ha])
  rwa [isRegularPoint_comp_torusActions_iff p, torusActions_actionAngleCover] at hz

/-! ### Almost existence -/

/-- **No level of a function of the actions has the contractible almost existence property.** For
`H = h(I)` with `h` of class `Cᵏ`, `k ≥ 2` and `k ≥ #ι`, almost every value of `h` is regular by
the Morse–Sard theorem, and no level of `H` carries a contractible closed characteristic. So no
level of `H`, regular or not, has the contractible almost existence property in any subset `W`. -/
theorem not_hasContractibleAlmostExistence_comp_torusActions {h : (ι → ℝ) → ℝ} {k : ℕ∞ω}
    (hh : ContDiff ℝ k h) (hk : 2 ≤ k) (hι : (Fintype.card ι : ℕ∞ω) ≤ k)
    (W : Set (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)))
    (c : ℝ) :
    ¬(symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle p)).HasContractibleAlmostExistence W (h ∘ torusActions p) c := by
  refine SmoothTwoForm.not_hasContractibleAlmostExistence_of_ae ?_
  -- Sard's regularity `#ι - 1 + 1` is at most `max #ι 1`, which `k` dominates.
  have hsard : ((Module.finrank ℝ (ι → ℝ) - Module.finrank ℝ ℝ + 1 : ℕ) : ℕ∞ω) ≤ k := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_self]
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · exact le_trans (by simp [h0]) hk
    · rwa [Nat.sub_add_cancel hpos]
  filter_upwards [hh.ae_forall_surjective_fderiv volume hsard] with c' hc'
  exact ⟨(isRegularValue_comp_torusActions_iff p).2 hc',
    not_hasContractibleClosedCharacteristic_comp_torusActions p (hh.of_le hk) W c'⟩

/-! ### The flat kinetic energy -/

/-- The **flat kinetic energy** `K = ½ ∑ⱼ I_j²` on the cotangent bundle of the torus: the kinetic
energy of the flat metric `∑ⱼ dθ_j²`, a function of the actions `I`. Its level `K = 1/2` is the unit
cosphere bundle of the flat torus. -/
def torusKineticEnergy :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) → ℝ :=
  (fun a : ι → ℝ ↦ (∑ j, a j ^ 2) / 2) ∘ torusActions p

/-- The flat kinetic energy of a covector is half the sum of the squares of its actions. -/
@[simp]
theorem torusKineticEnergy_apply
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) :
    torusKineticEnergy p z = (∑ j, torusActions p z j ^ 2) / 2 :=
  (rfl)

/-- The flat kinetic energy is the function `a ↦ ½ ∑ⱼ a_j²` of the actions. -/
theorem torusKineticEnergy_eq_comp :
    torusKineticEnergy (ι := ι) p = (fun a : ι → ℝ ↦ (∑ j, a j ^ 2) / 2) ∘ torusActions p :=
  (rfl)

omit [DecidableEq ι] in
/-- The profile `a ↦ ½ ∑ⱼ a_j²` of the flat kinetic energy is smooth. -/
private theorem contDiff_halfSumSq : ContDiff ℝ ω (fun a : ι → ℝ ↦ (∑ j, a j ^ 2) / 2) :=
  by fun_prop

/-- The flat kinetic energy is smooth. -/
theorem contMDiff_torusKineticEnergy :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ) ∞
      (torusKineticEnergy (ι := ι) p) :=
  (contDiff_halfSumSq.of_le le_top).contMDiff.comp (contMDiff_torusActions p)

/-- The flat kinetic energy vanishes on the zero section. -/
theorem torusKineticEnergy_zeroSection (x : ι → AddCircle p) :
    torusKineticEnergy p (zeroSection ((ι → ℝ) →L[ℝ] ℝ) (fun x : ι → AddCircle p ↦
      TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x →L[ℝ] ℝ) x) = 0 := by
  refine div_eq_zero_iff.2 (Or.inl (Finset.sum_eq_zero fun j _ ↦ ?_))
  rw [torusActions_apply, zeroSection_snd]
  -- The zero form on the tangent space at `x` takes the value `0` on the coordinate vector.
  exact zero_pow two_ne_zero

/-- **The sublevel sets of the flat kinetic energy are compact.** The actions of a covector with
`K ≤ b` are bounded, and the action map is proper. -/
theorem isCompact_preimage_Iic_torusKineticEnergy (b : ℝ) :
    IsCompact (torusKineticEnergy (ι := ι) p ⁻¹' Iic b) := by
  rw [torusKineticEnergy_eq_comp, preimage_comp]
  refine (isProperMap_torusActions p).isCompact_preimage
    (Metric.isCompact_of_isClosed_isBounded
      (isClosed_Iic.preimage contDiff_halfSumSq.continuous) ?_)
  -- Each action satisfies `|a_j| ≤ a_j² + 1 ≤ 2b + 1`.
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨2 * b + 1, fun a ha ↦ ?_⟩
  have hb : ∑ j, a j ^ 2 ≤ 2 * b := by
    have : (∑ j, a j ^ 2) / 2 ≤ b := ha
    linarith
  have hsum (i : ι) : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
    Finset.single_le_sum (f := fun j ↦ a j ^ 2) (fun j _ ↦ sq_nonneg (a j)) (Finset.mem_univ i)
  have hb0 : 0 ≤ 2 * b := le_trans (Finset.sum_nonneg fun j _ ↦ sq_nonneg (a j)) hb
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)]
  intro i
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (a i), sq_abs (a i), hsum i]

omit [DecidableEq ι] in
/-- The derivative of the profile `a ↦ ½ ∑ⱼ a_j²` of the flat kinetic energy, as produced by the
power and sum rules: `v ↦ ½ ∑ⱼ 2 a_j v_j`. -/
private theorem hasFDerivAt_halfSumSq (a : ι → ℝ) :
    HasFDerivAt (fun a : ι → ℝ ↦ (∑ j, a j ^ 2) / 2)
      ((2 : ℝ)⁻¹ • ∑ j, (2 • a j ^ (2 - 1)) • ContinuousLinearMap.proj (R := ℝ) j) a := by
  have hsum : HasFDerivAt (fun a : ι → ℝ ↦ ∑ j, a j ^ 2)
      (∑ j, (2 • a j ^ (2 - 1)) • ContinuousLinearMap.proj (R := ℝ) j) a :=
    HasFDerivAt.fun_sum fun j _ ↦ (hasFDerivAt_apply j a).pow 2
  simpa only [div_eq_mul_inv] using HasFDerivAt.mul_const hsum (2 : ℝ)⁻¹

/-- **Every nonzero value of the flat kinetic energy is regular.** At a covector with `K = c ≠ 0`
the actions `a` do not vanish, and the derivative of `½ ∑ⱼ a_j²` takes the value `∑ⱼ a_j² = 2c` on
`a` itself. -/
theorem isRegularValue_torusKineticEnergy {c : ℝ} (hc : c ≠ 0) :
    IsRegularValue ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ)
      (torusKineticEnergy (ι := ι) p) c := by
  rw [torusKineticEnergy_eq_comp, isRegularValue_comp_torusActions_iff p]
  intro a ha
  rw [(hasFDerivAt_halfSumSq a).fderiv]
  refine ContinuousLinearMap.surjective_iff_ne_zero.2 fun h0 ↦ hc ?_
  -- Evaluating the derivative at `a` gives `∑ⱼ a_j² = 2c`.
  have := DFunLike.congr_fun h0 a
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul, zero_apply,
    Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
  rw [← ha]
  have hsq : ∑ j, 2 * a j * a j = 2 * ∑ j, a j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hsq] at this
  linarith

/-- **No level of the flat kinetic energy has the contractible almost existence property**, in any
subset `W` of the cotangent bundle of the torus. In particular the unit cosphere bundle `K = 1/2`
of the flat torus, a regular level bounding the relatively compact domain `{K < 1/2}` around the
zero section, does not have it. -/
theorem not_hasContractibleAlmostExistence_torusKineticEnergy
    (W : Set (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)))
    (c : ℝ) :
    ¬(symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle p)).HasContractibleAlmostExistence W (torusKineticEnergy p) c :=
  not_hasContractibleAlmostExistence_comp_torusActions p contDiff_halfSumSq (by simp) le_top W c

end CotangentBundle

end TauCeti
