/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.OutermostStratum
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Hamiltonian
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.KineticEnergy
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

/-- **No level of the flat kinetic energy has the contractible almost existence property**, in any
subset `W` of the cotangent bundle of the torus. In particular the unit cosphere bundle `K = 1/2`
of the flat torus, a regular level bounding the relatively compact domain `{K < 1/2}` around the
zero section, does not have it. -/
theorem not_hasContractibleAlmostExistence_torusKineticEnergy
    (W : Set (CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)))
    (c : ℝ) :
    ¬(symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ι → AddCircle p)).HasContractibleAlmostExistence W (torusKineticEnergy p) c := by
  rw [torusKineticEnergy_eq_comp]
  exact not_hasContractibleAlmostExistence_comp_torusActions p (by fun_prop) (by simp) le_top W c

end CotangentBundle

end TauCeti
