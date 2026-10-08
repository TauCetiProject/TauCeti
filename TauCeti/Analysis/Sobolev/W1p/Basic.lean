/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.TestFunctionLp
import TauCeti.MeasureTheory.Function.Lp.Norm
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Analysis.Sobolev.GraphStep

/-!
# First-order weak Sobolev spaces

This file constructs the first-order, real-valued Sobolev space `W^{1,p}(Ω)` on an open subset
of a finite-dimensional real inner product space `E`. An element is an `Lᵖ` value-gradient jet
`(u, ∇u)` satisfying the distributional integration-by-parts pairing against test functions, and
this closed-subspace definition is identified with the weak Fréchet derivative predicate
`TauCeti.HasWeakFDerivOn`. The definitions do not assume finite dimension, but on an
infinite-dimensional `E` every compactly supported continuous function vanishes
(`HasCompactSupport.eq_zero_or_finiteDimensional`), so every test function is zero and every jet
is a member.

The quotient issue is handled at the definition boundary.  Both components of a jet are `Lp`
classes for `μ.restrict Ω`, and the weak relation is the one of the generic closed
weak-derivative graph `TauCeti.weakDerivStepSubmodule` over `Lᵖ(Ω)` with the identity base:
`TauCeti.w1pSubmodule` is its preimage under the continuous linear map that keeps the value and
reads the gradient as the field of functionals `⟪·, ∇u x⟫`.

Consequently the admissible jets form an intersection of kernels of continuous linear
functionals.  This makes `TauCeti.W1p` a closed subspace of the ambient Bochner `Lᵖ` space, and
hence complete when `E` is complete.
The theorem `TauCeti.mem_w1pSubmodule_iff_hasWeakFDerivOn` identifies this closed subspace
definition with the weak-derivative predicate, so the construction does not replace the
distributional condition by a merely formal closedness assumption.

The pointwise jet uses the Euclidean product norm on `ℝ × E`.  Thus at `p = 2` the inherited norm
is the usual Hilbert norm

`(‖u‖²₂ + ‖∇u‖²₂)¹⁄²`,

which is the space needed for energy methods in PDE.  No boundedness or
boundary regularity of `Ω` is used.

## Main declarations

* `TauCeti.Sobolev1Jet`: the value-gradient fibre `ℝ × E` with its Euclidean product norm.
* `TauCeti.w1pSubmodule`: the closed subspace of jets annihilating every weak-derivative test.
* `TauCeti.W1p`: the corresponding normed space (complete when `E` is complete).
* `TauCeti.mem_w1pSubmodule_iff_hasWeakFDerivOn`: membership is exactly weak
  differentiability of the value component with the recorded gradient.
* `TauCeti.W1p.valueL` and `TauCeti.W1p.gradientL`: the two components as continuous linear
  projections from the Sobolev space, with `TauCeti.W1p.value_coe` and
  `TauCeti.W1p.gradient_coe` identifying them with the components of the ambient jet.
* `TauCeti.W1p.locallyIntegrableOn_gradient`: the weak gradient is locally integrable on `Ω`.
* `TauCeti.W1p.gradient_ae_eq_zero_of_value_ae_eq_zero`: the weak gradient vanishes wherever
  the value vanishes on an open subset.
* `TauCeti.W1p.ofExponentLE`: on a domain of finite measure, `W^{1,q}(Ω) ⊆ W^{1,p}(Ω)` for
  `p ≤ q`.

## References

The graph-space construction and completeness argument follow L. C. Evans, *Partial Differential
Equations*, Chapter 5, §5.2.  The continuous annihilator presentation is the quotient-respecting
version of the standard proof that weak differentiation is a closed operator on `Lᵖ`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
variable {mu : Measure E} {Omega : Opens E} {p : ENNReal}

/-! ### Bochner `Lᵖ` Sobolev jets -/

/-- The fibre of a first-order scalar Sobolev jet: a value and its gradient, with the Euclidean
product norm. -/
abbrev Sobolev1Jet (E : Type*) :=
  WithLp 2 (ℝ × E)

/-- The ambient Bochner `Lᵖ` space of value-gradient jets on `Ω`. -/
abbrev Sobolev1JetLp (mu : Measure E) (Omega : Opens E) (p : ENNReal) :=
  Lp (Sobolev1Jet E) p (mu.restrict Omega)

private theorem memLp_assembleSobolev1Jet (u : Lp ℝ p (mu.restrict Omega))
    (g : Lp E p (mu.restrict Omega)) :
    MemLp (fun x => WithLp.toLp 2 (u x, g x)) p (mu.restrict Omega) := by
  apply MemLp.of_fst_of_snd_prodLp
  exact ⟨by simpa only [WithLp.toLp_fst] using Lp.memLp u,
    by simpa only [WithLp.toLp_snd] using Lp.memLp g⟩

private def assembleSobolev1JetLp (u : Lp ℝ p (mu.restrict Omega))
    (g : Lp E p (mu.restrict Omega)) : Sobolev1JetLp mu Omega p :=
  (memLp_assembleSobolev1Jet u g).toLp fun x => WithLp.toLp 2 (u x, g x)

private theorem assembleSobolev1JetLp_apply_ae (u : Lp ℝ p (mu.restrict Omega))
    (g : Lp E p (mu.restrict Omega)) :
    ∀ᵐ x ∂mu.restrict Omega,
      assembleSobolev1JetLp u g x = WithLp.toLp 2 (u x, g x) := by
  exact (memLp_assembleSobolev1Jet u g).coeFn_toLp

variable [InnerProductSpace ℝ E] [Fact (1 <= p)]

/-- The continuous linear projection from an `Lᵖ` Sobolev jet to its value component. -/
def Sobolev1JetLp.valueL :
    Sobolev1JetLp mu Omega p →L[ℝ] Lp ℝ p (mu.restrict Omega) :=
  (WithLp.fstL 2 ℝ ℝ E).compLpL p (mu.restrict Omega)

/-- The value component of an `Lᵖ` Sobolev jet. -/
def Sobolev1JetLp.value (J : Sobolev1JetLp mu Omega p) : Lp ℝ p (mu.restrict Omega) :=
  Sobolev1JetLp.valueL J

/-- Applying the bundled value projection gives the value component of a Sobolev jet. -/
@[simp]
theorem Sobolev1JetLp.valueL_apply (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.valueL J = Sobolev1JetLp.value J := (rfl)

/-- The bundled value projection is postcomposition with the first projection of the fibre. -/
theorem Sobolev1JetLp.valueL_eq_compLpL :
    Sobolev1JetLp.valueL (mu := mu) (Omega := Omega) (p := p) =
      (WithLp.fstL 2 ℝ ℝ E).compLpL p (mu.restrict Omega) := (rfl)

/-- The continuous linear projection from an `Lᵖ` Sobolev jet to its gradient component. -/
def Sobolev1JetLp.gradientL :
    Sobolev1JetLp mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
  (WithLp.sndL 2 ℝ ℝ E).compLpL p (mu.restrict Omega)

/-- The gradient component of an `Lᵖ` Sobolev jet. -/
def Sobolev1JetLp.gradient (J : Sobolev1JetLp mu Omega p) : Lp E p (mu.restrict Omega) :=
  Sobolev1JetLp.gradientL J

/-- Applying the bundled gradient projection gives the gradient component of a Sobolev jet. -/
@[simp]
theorem Sobolev1JetLp.gradientL_apply (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.gradientL J = Sobolev1JetLp.gradient J := (rfl)

/-- The bundled gradient projection is postcomposition with the second projection of the fibre. -/
theorem Sobolev1JetLp.gradientL_eq_compLpL :
    Sobolev1JetLp.gradientL (mu := mu) (Omega := Omega) (p := p) =
      (WithLp.sndL 2 ℝ ℝ E).compLpL p (mu.restrict Omega) := (rfl)

/-- The value component of a Sobolev jet is, almost everywhere on `Ω`, the first coordinate of the
jet. -/
@[simp]
theorem Sobolev1JetLp.value_apply_ae (J : Sobolev1JetLp mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      Sobolev1JetLp.value J x = WithLp.fst (J x) := by
  -- `coeFn_compLp` is stated for the unbundled `compLp`; expose that implementation of
  -- `valueL` so its pointwise theorem applies.
  change ∀ᵐ x ∂mu.restrict Omega,
    (WithLp.fstL 2 ℝ ℝ E).compLp J x = (WithLp.fstL 2 ℝ ℝ E) (J x)
  exact (WithLp.fstL 2 ℝ ℝ E).coeFn_compLp J

/-- The gradient component of a Sobolev jet is, almost everywhere on `Ω`, the second coordinate of
the jet. -/
@[simp]
theorem Sobolev1JetLp.gradient_apply_ae (J : Sobolev1JetLp mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      Sobolev1JetLp.gradient J x = WithLp.snd (J x) := by
  -- As for `value_apply_ae`, expose the unbundled `compLp` implementation consumed by
  -- Mathlib's pointwise coercion theorem.
  change ∀ᵐ x ∂mu.restrict Omega,
    (WithLp.sndL 2 ℝ ℝ E).compLp J x = (WithLp.sndL 2 ℝ ℝ E) (J x)
  exact (WithLp.sndL 2 ℝ ℝ E).coeFn_compLp J

/-- Two Sobolev jets are equal when their value and gradient components are equal. -/
@[ext]
theorem Sobolev1JetLp.ext {J K : Sobolev1JetLp mu Omega p}
    (hvalue : Sobolev1JetLp.value J = Sobolev1JetLp.value K)
    (hgradient : Sobolev1JetLp.gradient J = Sobolev1JetLp.gradient K) : J = K := by
  apply Lp.ext
  have hvalue_ae : Sobolev1JetLp.value J =ᵐ[mu.restrict Omega]
      Sobolev1JetLp.value K := by
    rwa [← Lp.ext_iff]
  have hgradient_ae : Sobolev1JetLp.gradient J =ᵐ[mu.restrict Omega]
      Sobolev1JetLp.gradient K := by
    rwa [← Lp.ext_iff]
  filter_upwards [Sobolev1JetLp.value_apply_ae J, Sobolev1JetLp.value_apply_ae K,
    Sobolev1JetLp.gradient_apply_ae J, Sobolev1JetLp.gradient_apply_ae K,
    hvalue_ae, hgradient_ae] with x hJvalue hKvalue hJgradient hKgradient hvalue hgradient
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).injective
  apply Prod.ext
  · simpa only [WithLp.prodContinuousLinearEquiv_apply, WithLp.fst, hJvalue, hKvalue] using hvalue
  · simpa only [WithLp.prodContinuousLinearEquiv_apply, WithLp.snd, hJgradient, hKgradient]
      using hgradient

/-- The norm of the value component is bounded by the norm of the ambient Sobolev jet. -/
private theorem norm_value_le_ambient (J : Sobolev1JetLp mu Omega p) :
    ‖Sobolev1JetLp.value J‖ ≤ ‖J‖ :=
  Lp.norm_le_norm_of_ae_le <| (Sobolev1JetLp.value_apply_ae J).mono fun x hx ↦ by
    rw [hx]
    exact WithLp.norm_fst_le ℝ (J x)

/-- The norm of the gradient component is bounded by the norm of the ambient Sobolev jet. -/
private theorem norm_gradient_le_ambient (J : Sobolev1JetLp mu Omega p) :
    ‖Sobolev1JetLp.gradient J‖ ≤ ‖J‖ :=
  Lp.norm_le_norm_of_ae_le <| (Sobolev1JetLp.gradient_apply_ae J).mono fun x hx ↦ by
    rw [hx]
    exact WithLp.norm_snd_le ℝ (J x)

/-- At exponent two, the Sobolev jet norm is the Hilbert graph norm of its components. -/
private theorem norm_sq_eq_norm_value_sq_add_norm_gradient_sq_ambient
    (J : Sobolev1JetLp mu Omega 2) :
    ‖J‖ ^ 2 = ‖Sobolev1JetLp.value J‖ ^ 2 + ‖Sobolev1JetLp.gradient J‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq J,
    ← real_inner_self_eq_norm_sq (Sobolev1JetLp.value J),
    ← real_inner_self_eq_norm_sq (Sobolev1JetLp.gradient J),
    L2.inner_def, L2.inner_def, L2.inner_def,
    ← integral_add (L2.integrable_inner (Sobolev1JetLp.value J) (Sobolev1JetLp.value J))
      (L2.integrable_inner (Sobolev1JetLp.gradient J) (Sobolev1JetLp.gradient J))]
  apply integral_congr_ae
  filter_upwards [Sobolev1JetLp.value_apply_ae J,
    Sobolev1JetLp.gradient_apply_ae J] with x hvalue hgradient
  rw [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, ← hvalue, ← hgradient]

/-- The candidate weak Fréchet derivative recorded by the gradient component of a Sobolev jet. -/
def Sobolev1JetLp.candidateWeakFDeriv (J : Sobolev1JetLp mu Omega p) : E → E →L[ℝ] ℝ :=
  fun x => innerSL ℝ (Sobolev1JetLp.gradient J x)

@[simp]
theorem Sobolev1JetLp.candidateWeakFDeriv_apply (J : Sobolev1JetLp mu Omega p) (x v : E) :
    Sobolev1JetLp.candidateWeakFDeriv J x v = ⟪v, Sobolev1JetLp.gradient J x⟫_ℝ := by
  rw [Sobolev1JetLp.candidateWeakFDeriv, innerSL_apply_apply, real_inner_comm]

@[simp]
private theorem value_assembleSobolev1JetLp (u : Lp ℝ p (mu.restrict Omega))
    (g : Lp E p (mu.restrict Omega)) :
    Sobolev1JetLp.value (assembleSobolev1JetLp u g) = u := by
  apply Lp.ext
  filter_upwards [Sobolev1JetLp.value_apply_ae (assembleSobolev1JetLp u g),
    assembleSobolev1JetLp_apply_ae u g] with x hvalue hassemble
  simpa only [hassemble, WithLp.toLp_fst] using hvalue

@[simp]
private theorem gradient_assembleSobolev1JetLp (u : Lp ℝ p (mu.restrict Omega))
    (g : Lp E p (mu.restrict Omega)) :
    Sobolev1JetLp.gradient (assembleSobolev1JetLp u g) = g := by
  apply Lp.ext
  filter_upwards [Sobolev1JetLp.gradient_apply_ae (assembleSobolev1JetLp u g),
    assembleSobolev1JetLp_apply_ae u g] with x hgradient hassemble
  simpa only [hassemble, WithLp.toLp_snd] using hgradient

/-! ### The weak Sobolev space `W^{1,p}(Ω)` -/

variable [OpensMeasurableSpace E]

private theorem testIntegral_eq_zero_iff
    (f f' : E → ℝ) (hf : LocallyIntegrableOn f Omega mu)
    (hf' : LocallyIntegrableOn f' Omega mu) (phi : 𝓓(Omega, ℝ)) (v : E) :
    (∫ x in Omega,
        lineDeriv ℝ (phi : E → ℝ) x v * f x + phi x * f' x ∂mu) = 0 ↔
      (∫ x, lineDeriv ℝ (phi : E → ℝ) x v • f x ∂mu) =
        -(∫ x, phi x • f' x ∂mu) := by
  have hleft : Integrable (fun x => lineDeriv ℝ (phi : E → ℝ) x v * f x) mu := by
    simpa only [smul_eq_mul] using integrable_lineDeriv_smul_of_locallyIntegrableOn hf phi v
  have hright : Integrable (fun x => phi x * f' x) mu := by
    simpa only [smul_eq_mul] using integrable_smul_of_locallyIntegrableOn hf' phi
  rw [integral_add hleft.integrableOn hright.integrableOn]
  simp only [← smul_eq_mul]
  rw [setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
    setIntegral_smul_eq_integral_smul]
  constructor <;> intro h <;> linarith

variable [mu.IsAddHaarMeasure]

/-- A value-gradient jet as a jet of `TauCeti.weakDerivStepSubmodule` over `Lᵖ(Ω)`: the value is
kept, and the `E`-valued gradient becomes the field of continuous linear functionals
`x ↦ ⟪·, ∇u x⟫`. -/
private def toWeakDerivStepJet :
    Sobolev1JetLp mu Omega p →L[ℝ]
      WeakDerivStepJetLp mu Omega p (Lp ℝ p (mu.restrict Omega)) ℝ :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (Sobolev1JetLp.valueL.prod
      (((innerSL ℝ (E := E)).compLpL p (mu.restrict Omega)).comp Sobolev1JetLp.gradientL))

omit [OpensMeasurableSpace E] [mu.IsAddHaarMeasure] in
/-- The first component of `toWeakDerivStepJet J` is the value of `J`. -/
private theorem fst_toWeakDerivStepJet (J : Sobolev1JetLp mu Omega p) :
    WithLp.fst (toWeakDerivStepJet J) = Sobolev1JetLp.value J := by
  simp only [toWeakDerivStepJet, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    WithLp.prodContinuousLinearEquiv_symm_apply, ContinuousLinearMap.prod_apply,
    WithLp.toLp_fst, Sobolev1JetLp.valueL_apply]

omit [OpensMeasurableSpace E] [mu.IsAddHaarMeasure] in
/-- The second component of `toWeakDerivStepJet J` is the gradient of `J`, read as the field of
functionals `x ↦ ⟪·, ∇u x⟫`. -/
private theorem snd_toWeakDerivStepJet (J : Sobolev1JetLp mu Omega p) :
    WithLp.snd (toWeakDerivStepJet J) =
      (innerSL ℝ (E := E)).compLpL p (mu.restrict Omega) (Sobolev1JetLp.gradient J) := by
  simp only [toWeakDerivStepJet, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    WithLp.prodContinuousLinearEquiv_symm_apply, ContinuousLinearMap.prod_apply,
    WithLp.toLp_snd, Sobolev1JetLp.gradientL_apply]

/-- The first-order weak Sobolev subspace: the preimage of the closed weak-derivative graph
`TauCeti.weakDerivStepSubmodule` over `Lᵖ(Ω)`, with the identity base, under the map reading the
gradient of a jet as a field of functionals.  Its members are the `Lᵖ` value-gradient jets
satisfying the weak integration-by-parts identity against every test function
(`TauCeti.mem_w1pSubmodule_iff`). -/
def w1pSubmodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] : ClosedSubmodule ℝ (Sobolev1JetLp mu Omega p) :=
  (weakDerivStepSubmodule mu Omega p
    (ContinuousLinearMap.id ℝ (Lp ℝ p (mu.restrict Omega)))).comap toWeakDerivStepJet

/-- Membership in `w1pSubmodule` is the family of weak integration-by-parts identities. -/
theorem mem_w1pSubmodule_iff (J : Sobolev1JetLp mu Omega p) :
    J ∈ w1pSubmodule mu Omega p ↔
      ∀ (phi : 𝓓(Omega, ℝ)) (v : E),
        ∫ x in Omega, (lineDeriv ℝ (phi : E → ℝ) x v * Sobolev1JetLp.value J x +
          phi x * Sobolev1JetLp.candidateWeakFDeriv J x v) ∂mu = 0 := by
  rw [w1pSubmodule, ClosedSubmodule.mem_comap, mem_weakDerivStepSubmodule_iff]
  refine forall₂_congr fun phi v => ?_
  symm
  let _ : (ENNReal.conjExponent p).HolderConjugate p := ENNReal.HolderConjugate.symm
  have hd : MemLp (fun x => lineDeriv ℝ (phi : E → ℝ) x v) (ENNReal.conjExponent p)
      (mu.restrict Omega) := by
    have hmem := memLp_testFunction (mu := mu) (ENNReal.conjExponent p)
      (TestFunction.lineDerivCLM ℝ v phi)
    rwa [show ((TestFunction.lineDerivCLM ℝ v phi : 𝓓(Omega, ℝ)) : E → ℝ) =
      fun x => lineDeriv ℝ (phi : E → ℝ) x v from
        funext fun _ => TestFunction.lineDerivCLM_apply_of_le le_top] at hmem
  have hcand : MemLp (fun x => Sobolev1JetLp.candidateWeakFDeriv J x v) p
      (mu.restrict Omega) := by
    simp only [Sobolev1JetLp.candidateWeakFDeriv_apply]
    exact (Lp.memLp (Sobolev1JetLp.gradient J)).const_inner v
  have h1 : Integrable (fun x => lineDeriv ℝ (phi : E → ℝ) x v * Sobolev1JetLp.value J x)
      (mu.restrict Omega) := hd.integrable_mul (Lp.memLp _)
  have h2 : Integrable (fun x => phi x * Sobolev1JetLp.candidateWeakFDeriv J x v)
      (mu.restrict Omega) :=
    (memLp_testFunction (mu := mu) (ENNReal.conjExponent p) phi).integrable_mul hcand
  have hsnd : (fun x => phi x • (WithLp.snd (toWeakDerivStepJet J) :
      Lp (E →L[ℝ] ℝ) p (mu.restrict Omega)) x v) =ᵐ[mu.restrict Omega]
      fun x => phi x * Sobolev1JetLp.candidateWeakFDeriv J x v := by
    rw [snd_toWeakDerivStepJet]
    filter_upwards [(innerSL ℝ (E := E)).coeFn_compLpL (μ := mu.restrict Omega) (p := p)
      (Sobolev1JetLp.gradient J)] with x hx
    rw [hx, smul_eq_mul, Sobolev1JetLp.candidateWeakFDeriv]
  rw [integral_add h1 h2, ← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
    ← setIntegral_smul_eq_integral_smul, integral_congr_ae hsnd, fst_toWeakDerivStepJet,
    ContinuousLinearMap.id_apply]
  simp only [smul_eq_mul]

/-- The first-order, real-valued weak Sobolev space `W^{1,p}(Ω)`, represented by its value and
weak gradient. -/
abbrev W1p (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 <= p)] := (w1pSubmodule mu Omega p).toSubmodule

/-- `W^{1,p}(Ω)` is complete in its value-gradient graph norm. -/
instance [CompleteSpace E] : CompleteSpace (W1p mu Omega p) :=
  (w1pSubmodule mu Omega p).isClosed.completeSpace_coe

/-- The continuous linear projection from `W1p` to its `Lᵖ` value component. -/
def W1p.valueL : W1p mu Omega p →L[ℝ] Lp ℝ p (mu.restrict Omega) :=
  Sobolev1JetLp.valueL.comp (w1pSubmodule mu Omega p).toSubmodule.subtypeL

/-- The `Lᵖ` value component of a Sobolev function. -/
def W1p.value (u : W1p mu Omega p) : Lp ℝ p (mu.restrict Omega) :=
  W1p.valueL u

@[simp]
theorem W1p.valueL_apply (u : W1p mu Omega p) : W1p.valueL u = W1p.value u := (rfl)

/-- The continuous linear projection from `W1p` to its `Lᵖ` weak-gradient component. -/
def W1p.gradientL : W1p mu Omega p →L[ℝ] Lp E p (mu.restrict Omega) :=
  Sobolev1JetLp.gradientL.comp (w1pSubmodule mu Omega p).toSubmodule.subtypeL

/-- The `Lᵖ` weak-gradient component of a Sobolev function. -/
def W1p.gradient (u : W1p mu Omega p) : Lp E p (mu.restrict Omega) :=
  W1p.gradientL u

@[simp]
theorem W1p.gradientL_apply (u : W1p mu Omega p) : W1p.gradientL u = W1p.gradient u := (rfl)

/-- `W1p.valueL` is the ambient jet projection precomposed with the inclusion, so the Sobolev
value component *is* the value component of the underlying ambient jet. -/
theorem W1p.value_coe (u : W1p mu Omega p) :
    W1p.value u = Sobolev1JetLp.value (u : Sobolev1JetLp mu Omega p) := (rfl)

/-- The Sobolev value component agrees almost everywhere with the first component of its
ambient value-gradient jet. -/
theorem W1p.value_apply_ae (u : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.value u x = WithLp.fst ((u : Sobolev1JetLp mu Omega p) x) := by
  rw [W1p.value_coe]
  exact Sobolev1JetLp.value_apply_ae (u : Sobolev1JetLp mu Omega p)

/-- The value of a finite sum of Sobolev functions is almost everywhere the sum of their values. -/
theorem W1p.value_finsetSum_ae {ι : Type*} (s : Finset ι) (u : ι → W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega, W1p.value (∑ j ∈ s, u j) x = ∑ j ∈ s, W1p.value (u j) x := by
  have h : W1p.value (∑ j ∈ s, u j) = ∑ j ∈ s, W1p.value (u j) := by
    simp only [← W1p.valueL_apply, map_sum]
  filter_upwards [Lp.coeFn_fun_finsetSum s fun j => W1p.value (u j)] with x hx
  rw [h, hx]


/-- As for `TauCeti.W1p.value_coe`: the Sobolev gradient component is the gradient component of
the underlying ambient jet. -/
theorem W1p.gradient_coe (u : W1p mu Omega p) :
    W1p.gradient u = Sobolev1JetLp.gradient (u : Sobolev1JetLp mu Omega p) := (rfl)

/-- The Sobolev gradient component agrees almost everywhere with the second component of its
ambient value-gradient jet. -/
theorem W1p.gradient_apply_ae (u : W1p mu Omega p) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.gradient u x = WithLp.snd ((u : Sobolev1JetLp mu Omega p) x) := by
  rw [W1p.gradient_coe]
  exact Sobolev1JetLp.gradient_apply_ae (u : Sobolev1JetLp mu Omega p)

/-- Two Sobolev functions are equal when their value and weak-gradient components are equal. -/
@[ext]
theorem W1p.ext {u v : W1p mu Omega p}
    (hvalue : W1p.value u = W1p.value v)
    (hgradient : W1p.gradient u = W1p.gradient v) : u = v :=
  Subtype.ext (Sobolev1JetLp.ext hvalue hgradient)

/-- The norm of a Sobolev function controls the norm of its value component. -/
theorem W1p.norm_value_le (u : W1p mu Omega p) : ‖W1p.value u‖ ≤ ‖u‖ :=
  norm_value_le_ambient u.1

/-- The norm of a Sobolev function controls the norm of its weak gradient. -/
theorem W1p.norm_gradient_le (u : W1p mu Omega p) : ‖W1p.gradient u‖ ≤ ‖u‖ :=
  norm_gradient_le_ambient u.1

/-- At exponent two, the norm on `W1p` is the Hilbert graph norm. -/
theorem W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq (u : W1p mu Omega 2) :
    ‖u‖ ^ 2 = ‖W1p.value u‖ ^ 2 + ‖W1p.gradient u‖ ^ 2 :=
  norm_sq_eq_norm_value_sq_add_norm_gradient_sq_ambient u.1

/-- The squared pointwise norm of a Sobolev gradient is integrable. -/
theorem W1p.integrable_norm_gradient_sq (u : W1p mu Omega 2) :
    Integrable (fun x => ‖W1p.gradient u x‖ ^ 2) (mu.restrict Omega) :=
  (memLp_two_iff_integrable_sq_norm (Lp.memLp (W1p.gradient u)).aestronglyMeasurable).1
    (Lp.memLp (W1p.gradient u))

/-- The squared pointwise value of a real Sobolev function is integrable. -/
theorem W1p.integrable_value_sq (u : W1p mu Omega 2) :
    Integrable (fun x => (W1p.value u x) ^ 2) (mu.restrict Omega) :=
  (Lp.memLp (W1p.value u)).integrable_sq

/-- The integral of the squared Sobolev gradient is its squared `L²` norm. -/
theorem W1p.integral_norm_gradient_sq_eq_norm_gradient_sq (u : W1p mu Omega 2) :
    ∫ x in Omega, ‖W1p.gradient u x‖ ^ 2 ∂mu = ‖W1p.gradient u‖ ^ 2 :=
  Lp.integral_norm_sq_eq_norm_sq (W1p.gradient u)

/-- The integral of the squared Sobolev value is its squared `L²` norm. -/
theorem W1p.integral_value_sq_eq_norm_value_sq (u : W1p mu Omega 2) :
    ∫ x in Omega, (W1p.value u x) ^ 2 ∂mu = ‖W1p.value u‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq (W1p.value u)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp [Real.norm_eq_abs, sq_abs])

/-- The `L²` pairing of the value components of two Sobolev functions, as an integral over `Ω`. -/
theorem W1p.inner_value_eq_setIntegral (u v : W1p mu Omega 2) :
    ⟪W1p.value u, W1p.value v⟫_ℝ = ∫ x in Omega, W1p.value u x * W1p.value v x ∂mu := by
  rw [L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp [RCLike.inner_apply, mul_comm])

/-- Convergence in the first-order Sobolev norm is equivalent to convergence of both the
value and the weak gradient in `Lᵖ`. -/
theorem W1p.tendsto_iff_value_gradient {I : Type*} {l : Filter I}
    {v : I → W1p mu Omega p} {u : W1p mu Omega p} :
    Filter.Tendsto v l (nhds u) ↔
      Filter.Tendsto (fun i => W1p.value (v i)) l (nhds (W1p.value u)) ∧
      Filter.Tendsto (fun i => W1p.gradient (v i)) l (nhds (W1p.gradient u)) := by
  constructor
  · intro h
    exact ⟨(W1p.valueL.continuous.tendsto u).comp h,
      (W1p.gradientL.continuous.tendsto u).comp h⟩
  · rintro ⟨hv, hg⟩
    let a : ℝ →L[ℝ] Sobolev1Jet E :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ ℝ E)
    let b : E →L[ℝ] Sobolev1Jet E :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr ℝ ℝ E)
    have heq (w : W1p mu Omega p) :
        w.1 = a.compLpL p (mu.restrict Omega) (W1p.value w) +
          b.compLpL p (mu.restrict Omega) (W1p.gradient w) := by
      apply Lp.ext
      filter_upwards [a.coeFn_compLpL (W1p.value w), b.coeFn_compLpL (W1p.gradient w),
        Lp.coeFn_add (a.compLpL p (mu.restrict Omega) (W1p.value w))
          (b.compLpL p (mu.restrict Omega) (W1p.gradient w)),
        W1p.value_apply_ae w, W1p.gradient_apply_ae w] with x ha hb hab hval hgrad
      rw [hab, Pi.add_apply, ha, hb]
      apply (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).injective
      simp only [WithLp.prodContinuousLinearEquiv_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply, ContinuousLinearEquiv.coe_coe,
        WithLp.prodContinuousLinearEquiv_symm_apply, ContinuousLinearMap.inr_apply,
        WithLp.ofLp_add, Prod.mk_add_mk, add_zero, zero_add, a, b]
      exact Prod.ext hval.symm hgrad.symm
    rw [tendsto_subtype_rng]
    simp_rw [heq]
    exact ((a.compLpL p (mu.restrict Omega)).continuous.tendsto _ |>.comp hv).add
      ((b.compLpL p (mu.restrict Omega)).continuous.tendsto _ |>.comp hg)

/-! ### Identification with weak Fréchet derivatives -/

section WeakDerivIdentification

variable [FiniteDimensional ℝ E]

/-- A jet belongs to `w1pSubmodule` exactly when its value component has the recorded gradient as
its weak Fréchet derivative. -/
theorem mem_w1pSubmodule_iff_hasWeakFDerivOn (J : Sobolev1JetLp mu Omega p) :
    J ∈ w1pSubmodule mu Omega p ↔
      HasWeakFDerivOn mu Omega (Sobolev1JetLp.value J)
        (Sobolev1JetLp.candidateWeakFDeriv J) := by
  have hvalue : LocallyIntegrableOn (Sobolev1JetLp.value J) Omega mu :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (Sobolev1JetLp.value J)).locallyIntegrable Fact.out)
  have hderiv (v : E) : LocallyIntegrableOn
      (fun x => Sobolev1JetLp.candidateWeakFDeriv J x v) Omega mu := by
    apply locallyIntegrableOn_of_locallyIntegrable_restrict
    have hinner := (Lp.memLp (Sobolev1JetLp.gradient J)).const_inner (𝕜 := ℝ) v
    exact (hinner.locallyIntegrable Fact.out).congr <| by
      filter_upwards with x
      simp only [Sobolev1JetLp.candidateWeakFDeriv_apply]
  rw [mem_w1pSubmodule_iff]
  constructor
  · intro h
    rw [hasWeakFDerivOn_iff]
    intro v
    rw [hasWeakLineDerivOn_iff_testFunction]
    refine ⟨inferInstance, hvalue, hderiv v, fun phi => ?_⟩
    exact (testIntegral_eq_zero_iff _ _ hvalue (hderiv v) phi v).mp (h phi v)
  · intro h
    rw [hasWeakFDerivOn_iff] at h
    intro phi v
    exact (testIntegral_eq_zero_iff _ _ (h v).locallyIntegrableOn
      (h v).locallyIntegrableOn_deriv phi v).mpr
        ((h v).integral_lineDeriv_smul_eq_neg_integral_smul phi)

/-- Construct a Sobolev function from its `Lᵖ` value and weak-gradient components. -/
def W1p.mk (u : Lp ℝ p (mu.restrict Omega)) (g : Lp E p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (g x))) : W1p mu Omega p :=
  ⟨assembleSobolev1JetLp u g, (mem_w1pSubmodule_iff_hasWeakFDerivOn _).mpr (by
    rw [value_assembleSobolev1JetLp]
    convert h using 1
    funext x
    rw [Sobolev1JetLp.candidateWeakFDeriv, gradient_assembleSobolev1JetLp])⟩

/-- The value component of `W1p.mk u g h` is `u`. -/
@[simp]
theorem W1p.value_mk (u : Lp ℝ p (mu.restrict Omega)) (g : Lp E p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (g x))) :
    W1p.value (W1p.mk u g h) = u :=
  value_assembleSobolev1JetLp u g

/-- The gradient component of `W1p.mk u g h` is `g`. -/
@[simp]
theorem W1p.gradient_mk (u : Lp ℝ p (mu.restrict Omega)) (g : Lp E p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega u (fun x => innerSL ℝ (g x))) :
    W1p.gradient (W1p.mk u g h) = g :=
  gradient_assembleSobolev1JetLp u g

/-- The value-gradient pair represented by an element of `W1p` satisfies the weak derivative
identity. -/
theorem W1p.hasWeakFDerivOn (u : W1p mu Omega p) :
    HasWeakFDerivOn mu Omega (W1p.value u)
      (fun x => innerSL ℝ (W1p.gradient u x)) :=
  (mem_w1pSubmodule_iff_hasWeakFDerivOn u.1).mp u.2

/-- The weak gradient of a Sobolev function is locally integrable on the domain, as its value
component is. -/
theorem W1p.locallyIntegrableOn_gradient (u : W1p mu Omega p) :
    LocallyIntegrableOn (W1p.gradient u : E → E) (Omega : Set E) mu :=
  locallyIntegrableOn_of_locallyIntegrable_restrict
    ((Lp.memLp (W1p.gradient u)).locallyIntegrable Fact.out)

section
variable [BorelSpace E]

/-- **A Sobolev function vanishing on an open subset has vanishing weak gradient there.** The
weak gradient is determined almost everywhere by the function on every open set
(`TauCeti.HasWeakFDerivOn.ae_eq`), and the zero function has zero weak gradient. -/
theorem W1p.gradient_ae_eq_zero_of_value_ae_eq_zero {V : Opens E} (hV : V ≤ Omega)
    {u : W1p mu Omega p} (hu : ∀ᵐ x ∂mu.restrict (V : Set E), W1p.value u x = 0) :
    ∀ᵐ x ∂mu.restrict (V : Set E), W1p.gradient u x = 0 := by
  have hzero : HasWeakFDerivOn mu V (W1p.value u) 0 :=
    hasWeakFDerivOn_zero.congr_ae (by filter_upwards [hu] with x hx; exact hx.symm)
  filter_upwards [((W1p.hasWeakFDerivOn u).mono hV).ae_eq hzero] with x hx
  have h0 : innerSL ℝ (W1p.gradient u x) = innerSL ℝ (0 : E) := by
    rw [map_zero]
    simpa using hx
  exact innerSL_inj.1 h0

/-- Two Sobolev functions are equal when their `Lᵖ` value components are equal.  Uniqueness of
weak derivatives determines the gradient component. -/
@[ext]
theorem W1p.ext_value {u v : W1p mu Omega p} (hvalue : W1p.value u = W1p.value v) : u = v := by
  apply W1p.ext hvalue
  apply Lp.ext
  have hderiv :
      (fun x => innerSL ℝ (W1p.gradient u x)) =ᵐ[mu.restrict Omega]
        fun x => innerSL ℝ (W1p.gradient v x) := by
    apply (W1p.hasWeakFDerivOn u).ae_eq
    simpa only [hvalue] using W1p.hasWeakFDerivOn v
  filter_upwards [hderiv] with x hx
  exact innerSL_inj.mp hx

end

end WeakDerivIdentification

section Exponent

variable {q : ENNReal} [Fact (1 <= q)] [IsFiniteMeasure (mu.restrict (Omega : Set E))]

/-- On a domain of finite measure, `W^{1,q}(Ω) ⊆ W^{1,p}(Ω)` for `p ≤ q`: the value and the
weak gradient of `u ∈ W^{1,q}(Ω)` are also in `Lᵖ(Ω)`, and are still related by the weak
derivative identity. -/
def W1p.ofExponentLE (hpq : p ≤ q) (u : W1p mu Omega q) : W1p mu Omega p :=
  ⟨⟨(u : Sobolev1JetLp mu Omega q).1, Lp.antitone hpq (u : Sobolev1JetLp mu Omega q).2⟩, by
    have hJ : (⟨(u : Sobolev1JetLp mu Omega q).1,
        Lp.antitone hpq (u : Sobolev1JetLp mu Omega q).2⟩ :
        Sobolev1JetLp mu Omega p) ∈ w1pSubmodule mu Omega p := by
      rw [mem_w1pSubmodule_iff]
      intro phi v
      have h_int := (mem_w1pSubmodule_iff (u : Sobolev1JetLp mu Omega q)).mp u.2 phi v
      have hae : (fun x => lineDeriv ℝ (phi : E → ℝ) x v *
          Sobolev1JetLp.value ⟨(u : Sobolev1JetLp mu Omega q).1,
            Lp.antitone hpq (u : Sobolev1JetLp mu Omega q).2⟩ x +
          phi x * Sobolev1JetLp.candidateWeakFDeriv ⟨(u : Sobolev1JetLp mu Omega q).1,
            Lp.antitone hpq (u : Sobolev1JetLp mu Omega q).2⟩ x v) =ᵐ[mu.restrict Omega]
          (fun x => lineDeriv ℝ (phi : E → ℝ) x v *
          Sobolev1JetLp.value (u : Sobolev1JetLp mu Omega q) x +
          phi x * Sobolev1JetLp.candidateWeakFDeriv (u : Sobolev1JetLp mu Omega q) x v) := by
        filter_upwards [Sobolev1JetLp.value_apply_ae ⟨(u : Sobolev1JetLp mu Omega q).1,
            Lp.antitone hpq (u : Sobolev1JetLp mu Omega q).2⟩,
          Sobolev1JetLp.value_apply_ae (u : Sobolev1JetLp mu Omega q),
          Sobolev1JetLp.gradient_apply_ae ⟨(u : Sobolev1JetLp mu Omega q).1,
            Lp.antitone hpq (u : Sobolev1JetLp mu Omega q).2⟩,
          Sobolev1JetLp.gradient_apply_ae (u : Sobolev1JetLp mu Omega q)]
          with x hval_p hval_q hgrad_p hgrad_q
        simp only [Sobolev1JetLp.candidateWeakFDeriv_apply]
        rw [hval_p, hval_q, hgrad_p, hgrad_q]
      rw [integral_congr_ae hae]
      exact h_int
    exact hJ⟩

/-- The underlying ambient `Lᵖ` jet of `W1p.ofExponentLE` is the canonical subtype inclusion of the
underlying `L^q` jet via `Lp.antitone`. -/
@[simp]
theorem W1p.coe_ofExponentLE (hpq : p ≤ q) (u : W1p mu Omega q) :
    (W1p.ofExponentLE hpq u : Sobolev1JetLp mu Omega p) =
      ⟨(u : Sobolev1JetLp mu Omega q).1, Lp.antitone hpq (u : Sobolev1JetLp mu Omega q).2⟩ :=
  (rfl)

/-- Lowering the exponent does not change the value of a Sobolev function. -/
theorem W1p.value_ofExponentLE_ae (hpq : p ≤ q) (u : W1p mu Omega q) :
    ⇑(W1p.value (W1p.ofExponentLE hpq u)) =ᵐ[mu.restrict Omega] W1p.value u := by
  rw [W1p.value_coe, W1p.value_coe, W1p.coe_ofExponentLE]
  filter_upwards [Sobolev1JetLp.value_apply_ae ⟨(u : Sobolev1JetLp mu Omega q).1,
      Lp.antitone hpq (u : Sobolev1JetLp mu Omega q).2⟩,
    Sobolev1JetLp.value_apply_ae (u : Sobolev1JetLp mu Omega q)] with x hp hq
  rw [hp, hq]

/-- Lowering the exponent does not change the weak gradient of a Sobolev function. -/
theorem W1p.gradient_ofExponentLE_ae (hpq : p ≤ q) (u : W1p mu Omega q) :
    ⇑(W1p.gradient (W1p.ofExponentLE hpq u)) =ᵐ[mu.restrict Omega] W1p.gradient u := by
  rw [W1p.gradient_coe, W1p.gradient_coe, W1p.coe_ofExponentLE]
  filter_upwards [Sobolev1JetLp.gradient_apply_ae ⟨(u : Sobolev1JetLp mu Omega q).1,
      Lp.antitone hpq (u : Sobolev1JetLp mu Omega q).2⟩,
    Sobolev1JetLp.gradient_apply_ae (u : Sobolev1JetLp mu Omega q)] with x hp hq
  rw [hp, hq]

/-- Coercion of `W1p.ofExponentLE` to the ambient jet space preserves zero. -/
theorem W1p.coe_ofExponentLE_zero (hpq : p ≤ q) :
    (W1p.ofExponentLE hpq (0 : W1p mu Omega q) : Sobolev1JetLp mu Omega p) = 0 :=
  Subtype.ext rfl

/-- Lowering the exponent sends zero to zero. -/
@[simp]
theorem W1p.ofExponentLE_zero (hpq : p ≤ q) :
    W1p.ofExponentLE hpq (0 : W1p mu Omega q) = 0 :=
  Subtype.ext (W1p.coe_ofExponentLE_zero hpq)

/-- Coercion of `W1p.ofExponentLE` to the ambient jet space preserves addition. -/
theorem W1p.coe_ofExponentLE_add (hpq : p ≤ q) (u v : W1p mu Omega q) :
    (W1p.ofExponentLE hpq (u + v) : Sobolev1JetLp mu Omega p) =
      (W1p.ofExponentLE hpq u : Sobolev1JetLp mu Omega p) +
        (W1p.ofExponentLE hpq v : Sobolev1JetLp mu Omega p) :=
  Subtype.ext rfl

/-- Lowering the exponent preserves addition. -/
@[simp]
theorem W1p.ofExponentLE_add (hpq : p ≤ q) (u v : W1p mu Omega q) :
    W1p.ofExponentLE hpq (u + v) = W1p.ofExponentLE hpq u + W1p.ofExponentLE hpq v :=
  Subtype.ext (W1p.coe_ofExponentLE_add hpq u v)

/-- Coercion of `W1p.ofExponentLE` to the ambient jet space preserves real scalar multiplication. -/
theorem W1p.coe_ofExponentLE_smul (hpq : p ≤ q) (c : ℝ) (u : W1p mu Omega q) :
    (W1p.ofExponentLE hpq (c • u) : Sobolev1JetLp mu Omega p) =
      c • (W1p.ofExponentLE hpq u : Sobolev1JetLp mu Omega p) :=
  Subtype.ext rfl

/-- Lowering the exponent preserves real scalar multiplication. -/
@[simp]
theorem W1p.ofExponentLE_smul (hpq : p ≤ q) (c : ℝ) (u : W1p mu Omega q) :
    W1p.ofExponentLE hpq (c • u) = c • W1p.ofExponentLE hpq u :=
  Subtype.ext (W1p.coe_ofExponentLE_smul hpq c u)

/-- Coercion of `W1p.ofExponentLE` to the ambient jet space at equal exponents is the identity. -/
theorem W1p.coe_ofExponentLE_self (u : W1p mu Omega p) :
    (W1p.ofExponentLE (le_refl p) u : Sobolev1JetLp mu Omega p) = u :=
  Subtype.ext rfl

/-- Lowering the exponent from `p` to itself is the identity. -/
@[simp]
theorem W1p.ofExponentLE_self (u : W1p mu Omega p) :
    W1p.ofExponentLE (le_refl p) u = u :=
  Subtype.ext (W1p.coe_ofExponentLE_self u)

/-- Coercions of composed ambient exponent inclusions compose transitively. -/
theorem W1p.coe_ofExponentLE_ofExponentLE {r : ENNReal} [Fact (1 ≤ r)]
    (hpq : p ≤ q) (hqr : q ≤ r) (u : W1p mu Omega r) :
    (W1p.ofExponentLE hpq (W1p.ofExponentLE hqr u) : Sobolev1JetLp mu Omega p) =
      (W1p.ofExponentLE (hpq.trans hqr) u : Sobolev1JetLp mu Omega p) :=
  Subtype.ext rfl

/-- Exponent inclusions compose transitively. -/
@[simp]
theorem W1p.ofExponentLE_ofExponentLE {r : ENNReal} [Fact (1 ≤ r)]
    (hpq : p ≤ q) (hqr : q ≤ r) (u : W1p mu Omega r) :
    W1p.ofExponentLE hpq (W1p.ofExponentLE hqr u) =
      W1p.ofExponentLE (hpq.trans hqr) u :=
  Subtype.ext (W1p.coe_ofExponentLE_ofExponentLE hpq hqr u)

end Exponent

end TauCeti
