/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.ChangeOfVariables
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Bounds
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Hessian

/-!
# Non-divergence-form equations under a change of variables

Let `Φ` be a change of variables of order two from an open set `U` onto an open set `V`, with
inverse `Ψ`, also of order two, and let `u ∈ W^{2,p}(V)`, `1 ≤ p < ∞`, be a strong solution of the
non-divergence-form equation

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` almost everywhere on `V`.

This file shows that `v = u ∘ Φ ∈ W^{2,p}(U)` is a strong solution of an equation of the same form
on `U` (`TauCeti.PDE.ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq`):

`tr (A' ∘ D²v) + ⟪b', ∇v⟫ + (c ∘ Φ) v = f ∘ Φ`,

with, at `x ∈ U`, `y = Φ x` and `M = DΨ(y)`,

* `A'(x) = M ∘ A(y) ∘ M†`, where `M†` is the adjoint of `M`;
* `b'(x) = M b(y) + ∑ᵢ D²Ψ(y) eᵢ (A(y)† eᵢ)` for any orthonormal basis `(eᵢ)`.

The second-order part transforms by conjugation, as for a linear change of variables, while the
curvature of `Ψ` contributes the first-order term `∑ᵢ D²Ψ(y) eᵢ (A(y)† eᵢ)`. Flattening the
boundary of a domain of class `C²` by such a change of variables turns an equation near a curved
boundary portion into one near a flat boundary portion, where the half-space estimates apply.

The new coefficients keep the properties those estimates ask of the old ones: `A'` is elliptic
where `A` is (`ContinuousLinearMap.mul_norm_sq_le_inner_comp_comp_adjoint`, with `M = DΨ(Φ x)` and
its right inverse `N = DΦ(x)`) and continuous where `A` is
(`TauCeti.PDE.continuousWithinAt_comp_comp_adjoint`), `A'` is measurable when `A` is
(`TauCeti.PDE.aestronglyMeasurable_comp_comp_adjoint`), and `b'` is measurable when `A` and `b`
are (`TauCeti.PDE.aestronglyMeasurable_fderiv_apply_add_sum`) and bounded when they are
(`TauCeti.PDE.norm_fderiv_apply_add_sum_le`).

The inverse change of variables is not needed: if `N(x)` is any right inverse of `DΦ(x)` on `U`,
then `v` solves
(`TauCeti.PDE.ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq_of_fderiv_comp_eq_id`)

`tr (A' ∘ D²v) + ⟪b', ∇v⟫ + (c ∘ Φ) v = f ∘ Φ`

with `A'(x) = N(x) A(Φ x) N(x)†` and `b'(x) = N(x) (b(Φ x) - ∑ᵢ D²Φ(x) eᵢ (A'(x)† eᵢ))`, where the
second derivatives of `Φ` itself produce the first-order correction.

For the standard orthonormal basis, the coefficients `A'` and `b'` of the first equation are
`TauCeti.PDE.nondivPullbackPrincipal` and `TauCeti.PDE.nondivPullbackDrift`, and the transformed
equation in these terms is
`TauCeti.PDE.ae_traceCLM_nondivPullbackPrincipal_comp_add_inner_nondivPullbackDrift_add_mul_eq`.
The structure the estimates need survives the change of variables: `A'` is elliptic
(`TauCeti.PDE.nondivPullbackPrincipal_elliptic`) and continuous
(`TauCeti.PDE.continuousWithinAt_nondivPullbackPrincipal`) wherever `A` is, `b'` is bounded
where `A` and `b` are (`TauCeti.PDE.norm_nondivPullbackDrift_le`), and both are measurable
(`TauCeti.PDE.aestronglyMeasurable_nondivPullbackPrincipal_and_nondivPullbackDrift`). For a change
of variables `Φ` of the whole space that is Lipschitz with `Φ_* μ ≤ K μ`, such as the shear
flattening a graph, and `DΨ ∘ Φ` bounded and uniformly continuous, `A'` has vanishing mean
oscillation when `A` is bounded and has vanishing mean oscillation
(`TauCeti.PDE.memVMO_nondivPullbackPrincipal`), as the `W^{2,p}` estimates for coefficients of
vanishing mean oscillation require.

## The argument

Since `Φ ∘ Ψ` is the identity on `V`, `u = v ∘ Ψ`, and the chain rule for the weak Hessian
(`TauCeti.Wkp.inner_iteratedGradient_compL_ae`) gives

`⟪D²u(y) f, g⟫ = ⟪D²v(Ψ y) (M f), M g⟫ + ⟪∇v(Ψ y), D²Ψ(y) f g⟫`,

with `∇u(y) = M† ∇v(Ψ y)` and `u(y) = v(Ψ y)`. Computing the trace in the basis `(eᵢ)`,
`tr (A ∘ D²u) = ∑ᵢ ⟪D²u(y) eᵢ, A† eᵢ⟫`, and the cyclicity of the trace,
`tr (A ∘ M† ∘ D²v ∘ M) = tr (M ∘ A ∘ M† ∘ D²v)`, rewrite the equation at `y` in terms of `v` at
`Ψ y`. Pulling it back along `Φ` gives the equation for `v` at almost every `x ∈ U`.

For the variant with a right inverse `N(x)` of `M(x) = DΦ(x)`, the chain rule along `Φ` writes
`D²v(x) = M† ∘ D²u(Φ x) ∘ M + H` with `H f = (D²Φ(x) f)† ∇u(Φ x)`. Since `M N = 1`, the first part
contributes `tr (A' ∘ M† ∘ D²u(Φ x) ∘ M) = tr (A(Φ x) ∘ D²u(Φ x))`, while `tr (A' ∘ H)` is the
first-order term `⟪∑ᵢ D²Φ(x) eᵢ (A'† eᵢ), ∇u(Φ x)⟫`, and `⟪N z, ∇v⟫ = ⟪z, ∇u(Φ x)⟫`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 and the proof of Theorem 9.13 (flattening the boundary transforms the operator into
  one of the same form).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2 (flattening the boundary).
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace NNReal

namespace TauCeti.PDE

open Wkp

section Coefficients

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {U U' : Opens F} {Φ Ψ : F → F} {L L' c c' : ℝ}

/-- Conjugating coefficients continuous within `Ω` at `Φ x` by `DΨ ∘ Φ`, for a change of
variables `Ψ` of order at least one on `U ∋ Φ x` and `Φ` continuous within `Ω'` at `x` mapping
`Ω'` into `Ω`, gives coefficients continuous within `Ω'` at `x`. -/
theorem continuousWithinAt_comp_comp_adjoint {Ω Ω' : Set F} {k : ℕ}
    (hΨ : IsChangeOfVariables (k + 1) U U' Ψ L' c') {A : F → F →L[ℝ] F} {x : F}
    (hΦx : ContinuousWithinAt Φ Ω' x) (hΦxU : Φ x ∈ (U : Set F)) (hmaps : MapsTo Φ Ω' Ω)
    (hA : ContinuousWithinAt A Ω (Φ x)) :
    ContinuousWithinAt
      (fun x => fderiv ℝ Ψ (Φ x) ∘L A (Φ x) ∘L (fderiv ℝ Ψ (Φ x)).adjoint) Ω' x := by
  have hM : ContinuousWithinAt (fun x => fderiv ℝ Ψ (Φ x)) Ω' x :=
    ((hΨ.contDiffOn.continuousOn_fderiv_of_isOpen U.isOpen (by simp)).continuousAt
      (U.isOpen.mem_nhds hΦxU)).comp_continuousWithinAt hΦx
  exact hM.clm_comp ((hA.comp hΦx hmaps).clm_comp
    (ContinuousLinearMap.adjoint.continuous.continuousAt.comp_continuousWithinAt hM))

/-- **The transformed principal part is measurable.** For a change of variables `Ψ` of order at
least one from `U`, a map `Φ` continuous on a measurable set `s` and mapping it into `U`, and
coefficients `A ∘ Φ` almost everywhere strongly measurable on `s`, the principal part
`DΨ ∘ A ∘ DΨ†` of the transformed equation, evaluated at `Φ x`, is almost everywhere strongly
measurable on `s`. -/
theorem aestronglyMeasurable_comp_comp_adjoint {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] {μ : Measure F} {U U' : Opens F} {Ψ : F → F} {k : ℕ} {L' c' : ℝ}
    (hΨ : IsChangeOfVariables (k + 1) U U' Ψ L' c') {s : Set F} (hs : MeasurableSet s)
    {Φ : F → F} (hΦc : ContinuousOn Φ s) (hΦU : MapsTo Φ s U) {A : F → F →L[ℝ] F}
    (hA : AEStronglyMeasurable (fun x => A (Φ x)) (μ.restrict s)) :
    AEStronglyMeasurable
      (fun x => fderiv ℝ Ψ (Φ x) ∘L A (Φ x) ∘L (fderiv ℝ Ψ (Φ x)).adjoint) (μ.restrict s) := by
  have hM : ContinuousOn (fun x => fderiv ℝ Ψ (Φ x)) s :=
    (hΨ.contDiffOn.continuousOn_fderiv_of_isOpen U.isOpen (by simp)).comp hΦc hΦU
  have hcomp := (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := F) (F := F) (G := F)).continuous
  exact hcomp.comp_aestronglyMeasurable₂ (hM.aestronglyMeasurable hs)
    (hcomp.comp_aestronglyMeasurable₂ hA
      ((ContinuousLinearMap.adjoint.continuous.comp_continuousOn hM).aestronglyMeasurable hs))

/-- **The transformed first-order coefficient is measurable.** For a change of variables `Ψ` of
order at least two from `U`, a map `Φ` continuous on a measurable set `s` and mapping it into `U`,
coefficients `A ∘ Φ` and `b ∘ Φ` almost everywhere strongly measurable on `s`, and an orthonormal
basis `(eᵢ)`, the first-order coefficient `DΨ b + ∑ᵢ D²Ψ eᵢ (A† eᵢ)` of the transformed equation,
evaluated at `Φ x`, is almost everywhere strongly measurable on `s`. -/
theorem aestronglyMeasurable_fderiv_apply_add_sum {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F]
    [BorelSpace F] {μ : Measure F} {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ F)
    {U U' : Opens F} {Ψ : F → F} {k : ℕ} {L' c' : ℝ}
    (hΨ : IsChangeOfVariables (k + 2) U U' Ψ L' c') {s : Set F} (hs : MeasurableSet s)
    {Φ : F → F} (hΦc : ContinuousOn Φ s) (hΦU : MapsTo Φ s U) {A : F → F →L[ℝ] F} {b : F → F}
    (hA : AEStronglyMeasurable (fun x => A (Φ x)) (μ.restrict s))
    (hb : AEStronglyMeasurable (fun x => b (Φ x)) (μ.restrict s)) :
    AEStronglyMeasurable (fun x => fderiv ℝ Ψ (Φ x) (b (Φ x)) +
      ∑ i, fderiv ℝ (fderiv ℝ Ψ) (Φ x) (e i) ((A (Φ x)).adjoint (e i))) (μ.restrict s) := by
  -- The first and second derivatives of `Ψ` along `Φ` are continuous on `s`.
  have hM : ContinuousOn (fun x => fderiv ℝ Ψ (Φ x)) s :=
    (hΨ.contDiffOn.continuousOn_fderiv_of_isOpen U.isOpen (by norm_cast; omega)).comp hΦc hΦU
  have hS : ContinuousOn (fun x => fderiv ℝ (fderiv ℝ Ψ) (Φ x)) s :=
    (ContDiffOn.continuousOn_fderiv_of_isOpen
      (hΨ.contDiffOn.fderiv_of_isOpen U.isOpen (m := 1) (by norm_cast; omega)) U.isOpen
      le_rfl).comp hΦc hΦU
  have happly := (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := F) (F := F)).continuous
  refine (happly.comp_aestronglyMeasurable₂ (hM.aestronglyMeasurable hs) hb).add
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_)
  exact happly.comp_aestronglyMeasurable₂
    ((hS.clm_apply continuousOn_const).aestronglyMeasurable hs)
    ((ContinuousLinearMap.apply ℝ F (e i)).continuous.comp_aestronglyMeasurable
      (ContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable hA))

/-- **The pulled-back drift is bounded.** For a change of variables `Ψ` of order at least two from
`U` with constant `L'`, coefficients `‖A‖ ≤ Λ` and `‖b‖ ≤ β`, and an orthonormal basis `(eᵢ)`, the
first-order coefficient `DΨ b + ∑ᵢ D²Ψ eᵢ (A† eᵢ)` of the transformed equation has norm at most
`L' β + n L' Λ`. -/
theorem norm_fderiv_apply_add_sum_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ F) {U U' : Opens F}
    {Ψ : F → F} {k : ℕ} {L' c' : ℝ} (hΨ : IsChangeOfVariables (k + 2) U U' Ψ L' c') {y : F}
    (hy : y ∈ (U : Set F)) {A₀ : F →L[ℝ] F} {b₀ : F} {Λ β : ℝ} (hA₀ : ‖A₀‖ ≤ Λ)
    (hb₀ : ‖b₀‖ ≤ β) :
    ‖fderiv ℝ Ψ y b₀ + ∑ i, fderiv ℝ (fderiv ℝ Ψ) y (e i) (A₀.adjoint (e i))‖ ≤
      L' * β + Fintype.card ι * (L' * Λ) := by
  have hD := hΨ.norm_fderiv_le y hy
  have hD2 := hΨ.norm_fderiv_fderiv_le y hy
  have hL' : 0 ≤ L' := (norm_nonneg _).trans hD
  have hterm (i : ι) : ‖fderiv ℝ (fderiv ℝ Ψ) y (e i) (A₀.adjoint (e i))‖ ≤ L' * Λ := by
    refine ((fderiv ℝ (fderiv ℝ Ψ) y).le_opNorm₂ _ _).trans ?_
    rw [e.norm_eq_one, mul_one]
    refine mul_le_mul hD2 ((A₀.adjoint.le_opNorm _).trans ?_) (norm_nonneg _) hL'
    rw [LinearIsometryEquiv.norm_map, e.norm_eq_one, mul_one]
    exact hA₀
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ((fderiv ℝ Ψ y).le_opNorm _).trans (mul_le_mul hD hb₀ (norm_nonneg _) hL')
  · refine (norm_sum_le _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i

end Coefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The trace of `A ∘ D²u` for `D²u` given by the chain rule
`⟪D²u f, g⟫ = ⟪D (M f), M g⟫ + ⟪w, S f g⟫`: it is `tr ((M ∘ A ∘ M†) ∘ D) + ∑ᵢ ⟪S eᵢ (A† eᵢ), w⟫`
for any orthonormal basis `(eᵢ)`. -/
private theorem traceCLM_comp_eq_of_forall_inner_eq {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) {A H M D : E →L[ℝ] E} {S : E →L[ℝ] E →L[ℝ] E} {w : E}
    (hH : ∀ f g : E, ⟪H f, g⟫_ℝ = ⟪D (M f), M g⟫_ℝ + ⟪w, S f g⟫_ℝ) :
    traceCLM ℝ E (A ∘L H) =
      traceCLM ℝ E ((M ∘L A ∘L M.adjoint) ∘L D) + ∑ i, ⟪S (e i) (A.adjoint (e i)), w⟫_ℝ := by
  have hcyc : traceCLM ℝ E ((M ∘L A ∘L M.adjoint) ∘L D) =
      traceCLM ℝ E (A ∘L (M.adjoint ∘L D ∘L M)) := by
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.traceCLM_comp_comm]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [hcyc, traceCLM_apply, traceCLM_apply, LinearMap.trace_eq_sum_inner _ e,
    LinearMap.trace_eq_sum_inner _ e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_coe,
    ← ContinuousLinearMap.adjoint_inner_left A, ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm, hH, real_inner_comm (M _), real_inner_comm w]

variable {U V : Opens E} {Φ Ψ : E → E} {L L' c c' : ℝ}

/-- The principal coefficient `x ↦ DΨ(Φ x) ∘ A(Φ x) ∘ DΨ(Φ x)†` of the equation satisfied by `u ∘ Φ`
when `u` solves `tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u = f` and `Ψ` is the inverse of `Φ`. -/
noncomputable def nondivPullbackPrincipal (Φ Ψ : E → E) (A : E → E →L[ℝ] E) (x : E) :
    E →L[ℝ] E :=
  fderiv ℝ Ψ (Φ x) ∘L A (Φ x) ∘L (fderiv ℝ Ψ (Φ x)).adjoint

/-- The drift `x ↦ DΨ(Φ x) b(Φ x) + ∑ᵢ D²Ψ(Φ x) (eᵢ, A(Φ x)† eᵢ)` of the equation satisfied by
`u ∘ Φ`, for the standard orthonormal basis `(eᵢ)`. -/
noncomputable def nondivPullbackDrift (Φ Ψ : E → E) (A : E → E →L[ℝ] E) (b : E → E) (x : E) : E :=
  fderiv ℝ Ψ (Φ x) (b (Φ x)) + ∑ i, iteratedFDeriv ℝ 2 Ψ (Φ x)
    ![stdOrthonormalBasis ℝ E i, (A (Φ x)).adjoint (stdOrthonormalBasis ℝ E i)]

/-- The value of the pulled-back principal coefficient: `A'(x) = DΨ(Φ x) ∘ A(Φ x) ∘ DΨ(Φ x)†`. -/
theorem nondivPullbackPrincipal_apply (Φ Ψ : E → E) (A : E → E →L[ℝ] E) (x : E) :
    nondivPullbackPrincipal Φ Ψ A x =
      fderiv ℝ Ψ (Φ x) ∘L A (Φ x) ∘L (fderiv ℝ Ψ (Φ x)).adjoint :=
  (rfl)

/-- The value of the pulled-back drift:
`b'(x) = DΨ(Φ x) b(Φ x) + ∑ᵢ D²Ψ(Φ x) (eᵢ, A(Φ x)† eᵢ)` for the standard orthonormal basis. -/
theorem nondivPullbackDrift_apply (Φ Ψ : E → E) (A : E → E →L[ℝ] E) (b : E → E) (x : E) :
    nondivPullbackDrift Φ Ψ A b x = fderiv ℝ Ψ (Φ x) (b (Φ x)) + ∑ i, iteratedFDeriv ℝ 2 Ψ (Φ x)
      ![stdOrthonormalBasis ℝ E i, (A (Φ x)).adjoint (stdOrthonormalBasis ℝ E i)] :=
  (rfl)

/-- The pulled-back principal coefficient `A'` is elliptic wherever `A` is: if
`λ ‖η‖² ≤ ⟪A(Φ x) η, η⟫` and `‖DΦ(x)‖ ≤ L`, then `λ / max L 1 ^ 2 ‖ξ‖² ≤ ⟪A'(x) ξ, ξ⟫`. -/
theorem nondivPullbackPrincipal_elliptic {k k' : ℕ}
    (hΦ : IsChangeOfVariables (k + 1) U V Φ L c) (hΨ : IsChangeOfVariables k' V U Ψ L' c')
    (hΨΦ : LeftInvOn Ψ Φ U) (hΦΨ : RightInvOn Ψ Φ V) {A : E → E →L[ℝ] E} {x : E} (hx : x ∈ U)
    {lam : ℝ} (hlam : 0 < lam) (hA : ∀ η, lam * ‖η‖ ^ 2 ≤ ⟪A (Φ x) η, η⟫_ℝ) :
    0 < lam / max L 1 ^ 2 ∧
      ∀ ξ, lam / max L 1 ^ 2 * ‖ξ‖ ^ 2 ≤ ⟪nondivPullbackPrincipal Φ Ψ A x ξ, ξ⟫_ℝ := by
  refine ⟨by positivity, fun ξ => ?_⟩
  set N := fderiv ℝ Ψ (Φ x)
  -- `ξ = DΦ(x)† (N† ξ)`, since `N ∘ DΦ(x) = id`.
  have hid : N ∘L fderiv ℝ Φ x = ContinuousLinearMap.id ℝ E :=
    hΦ.fderiv_comp_fderiv_eq_id hΨ hΨΦ hΦΨ hx
  have hξ : (fderiv ℝ Φ x).adjoint (N.adjoint ξ) = ξ := by
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp, hid,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
  have hnorm : ‖ξ‖ ≤ max L 1 * ‖N.adjoint ξ‖ := by
    calc ‖ξ‖ = ‖(fderiv ℝ Φ x).adjoint (N.adjoint ξ)‖ := by rw [hξ]
      _ ≤ ‖(fderiv ℝ Φ x).adjoint‖ * ‖N.adjoint ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ max L 1 * ‖N.adjoint ξ‖ := by
        gcongr
        rw [LinearIsometryEquiv.norm_map]
        exact (hΦ.norm_fderiv_le x hx).trans (le_max_left _ _)
  have hinner :
      ⟪nondivPullbackPrincipal Φ Ψ A x ξ, ξ⟫_ℝ = ⟪A (Φ x) (N.adjoint ξ), N.adjoint ξ⟫_ℝ := by
    simp only [nondivPullbackPrincipal_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [hinner]
  calc lam / max L 1 ^ 2 * ‖ξ‖ ^ 2 ≤ lam / max L 1 ^ 2 * (max L 1 * ‖N.adjoint ξ‖) ^ 2 := by
        gcongr
    _ = lam * ‖N.adjoint ξ‖ ^ 2 := by field_simp
    _ ≤ _ := hA _

/-- The pulled-back principal coefficient is continuous within `s` at `x` when `Φ` maps `s` into
`t`, `Φ x ∈ V` and `A` is continuous within `t` at `Φ x`. -/
theorem continuousWithinAt_nondivPullbackPrincipal {k : ℕ}
    (hΨ : IsChangeOfVariables (k + 1) V U Ψ L' c')
    {x : E} (hΦc : ContinuousAt Φ x) {s t : Set E} (hst : MapsTo Φ s t) {A : E → E →L[ℝ] E}
    (hxV : Φ x ∈ V) (hA : ContinuousWithinAt A t (Φ x)) :
    ContinuousWithinAt (nondivPullbackPrincipal Φ Ψ A) s x := by
  have hM : ContinuousAt (fun y => fderiv ℝ Ψ (Φ y)) x :=
    ((hΨ.contDiffOn.continuousOn_fderiv_of_isOpen V.isOpen
      (by exact_mod_cast le_add_self)).continuousAt (V.isOpen.mem_nhds hxV)).comp hΦc
  have hconj : Continuous fun q : (E →L[ℝ] E) × (E →L[ℝ] E) => q.1 ∘L q.2 ∘L q.1.adjoint := by
    fun_prop
  exact hconj.continuousAt.comp_continuousWithinAt
    (hM.continuousWithinAt.prodMk (hA.comp hΦc.continuousWithinAt hst))

/-- The drift of the pulled-back equation is bounded by `L' β + n L' Λ`, `n = dim E`, at points
where `‖b(Φ x)‖ ≤ β` and `‖A(Φ x)‖ ≤ Λ`. -/
theorem norm_nondivPullbackDrift_le (hΨ : IsChangeOfVariables 2 V U Ψ L' c')
    {A : E → E →L[ℝ] E} {b : E → E} {x : E} (hxV : Φ x ∈ V) {β Λ : ℝ} (hb : ‖b (Φ x)‖ ≤ β)
    (hA : ‖A (Φ x)‖ ≤ Λ) :
    ‖nondivPullbackDrift Φ Ψ A b x‖ ≤ L' * β + Module.finrank ℝ E * (L' * Λ) := by
  have hL' : ‖fderiv ℝ Ψ (Φ x)‖ ≤ L' := hΨ.norm_fderiv_le (Φ x) hxV
  have hL'' : ‖iteratedFDeriv ℝ 2 Ψ (Φ x)‖ ≤ L' :=
    hΨ.norm_iteratedFDeriv_le 2 one_le_two le_rfl (Φ x) hxV
  have h0 : 0 ≤ L' := (norm_nonneg _).trans hL'
  have hterm : ∀ i, ‖iteratedFDeriv ℝ 2 Ψ (Φ x)
      ![stdOrthonormalBasis ℝ E i, (A (Φ x)).adjoint (stdOrthonormalBasis ℝ E i)]‖ ≤ L' * Λ :=
    fun i => by
      refine ((iteratedFDeriv ℝ 2 Ψ (Φ x)).le_opNorm _).trans ?_
      simp only [Fin.prod_univ_two, Matrix.cons_val, (stdOrthonormalBasis ℝ E).orthonormal.1 i,
        one_mul]
      have ha : ‖(A (Φ x)).adjoint (stdOrthonormalBasis ℝ E i)‖ ≤ Λ := by
        refine ((A (Φ x)).adjoint.le_opNorm _).trans ?_
        rw [LinearIsometryEquiv.norm_map, (stdOrthonormalBasis ℝ E).orthonormal.1 i, mul_one]
        exact hA
      exact mul_le_mul hL'' ha (norm_nonneg _) h0
  rw [nondivPullbackDrift_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ((fderiv ℝ Ψ (Φ x)).le_opNorm _).trans (mul_le_mul hL' hb (norm_nonneg _) h0)
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖iteratedFDeriv ℝ 2 Ψ (Φ x)
            ![stdOrthonormalBasis ℝ E i, (A (Φ x)).adjoint (stdOrthonormalBasis ℝ E i)]‖
        ≤ ∑ _i : Fin (Module.finrank ℝ E), L' * Λ := Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by simp

variable [MeasurableSpace E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

omit [mu.IsAddHaarMeasure] in
/-- The coefficients of the pulled-back equation are almost everywhere strongly measurable on an
open set `s` that `Φ` maps into `V`, when `A ∘ Φ` and `b ∘ Φ` are. -/
theorem aestronglyMeasurable_nondivPullbackPrincipal_and_nondivPullbackDrift
    (hΨ : IsChangeOfVariables 2 V U Ψ L' c') {s : Set E} (hΦc : ContinuousOn Φ s)
    (hs : MeasurableSet s) (hsV : MapsTo Φ s V) {A : E → E →L[ℝ] E} {b : E → E}
    (hA : AEStronglyMeasurable (fun x => A (Φ x)) (mu.restrict s))
    (hb : AEStronglyMeasurable (fun x => b (Φ x)) (mu.restrict s)) :
    AEStronglyMeasurable (nondivPullbackPrincipal Φ Ψ A) (mu.restrict s) ∧
      AEStronglyMeasurable (nondivPullbackDrift Φ Ψ A b) (mu.restrict s) := by
  have hM : AEStronglyMeasurable (fun x => fderiv ℝ Ψ (Φ x)) (mu.restrict s) :=
    ((hΨ.contDiffOn.continuousOn_fderiv_of_isOpen V.isOpen (by norm_num)).comp
      hΦc hsV).aestronglyMeasurable hs
  have hD2 : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ 2 Ψ (Φ x)) (mu.restrict s) :=
    (((hΨ.contDiffOn.continuousOn_iteratedFDerivWithin le_rfl V.isOpen.uniqueDiffOn).congr
      fun y hy => (iteratedFDerivWithin_of_isOpen 2 V.isOpen hy).symm).comp
        hΦc hsV).aestronglyMeasurable hs
  have hconj : Continuous fun q : (E →L[ℝ] E) × (E →L[ℝ] E) => q.1 ∘L q.2 ∘L q.1.adjoint := by
    fun_prop
  have happ : Continuous fun q : (E →L[ℝ] E) × E => q.1 q.2 := by fun_prop
  refine ⟨hconj.comp_aestronglyMeasurable₂ (g := fun M A => M ∘L A ∘L M.adjoint) hM hA,
    (happ.comp_aestronglyMeasurable₂ (g := fun M v => M v) hM hb).add
      (Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_)⟩
  have hev : Continuous fun q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E × (E →L[ℝ] E) =>
      q.1 ![stdOrthonormalBasis ℝ E i, q.2.adjoint (stdOrthonormalBasis ℝ E i)] := by
    fun_prop
  exact hev.comp_aestronglyMeasurable₂
    (g := fun T A => T ![stdOrthonormalBasis ℝ E i, A.adjoint (stdOrthonormalBasis ℝ E i)]) hD2 hA

/-- **The pulled-back principal coefficient has vanishing mean oscillation.** Let `Φ : E → E` be
Lipschitz with `Φ_* μ ≤ K μ`, as for the shear flattening the graph of a Lipschitz function, which
preserves `μ`, and let `M(x) = DΨ(Φ x)` be bounded and uniformly continuous on `E`. If the
coefficient field `A` is essentially bounded and has vanishing mean oscillation, then so does the
pulled-back coefficient `A'(x) = M(x) ∘ A(Φ x) ∘ M(x)†`. -/
theorem memVMO_nondivPullbackPrincipal {A : E → E →L[ℝ] E} (hA : MemVMO A mu) {Λ N L K : ℝ≥0}
    (hAΛ : ∀ᵐ y ∂mu, ‖A y‖ ≤ Λ) (hΦ : LipschitzWith L Φ) (hmap : mu.map Φ ≤ K • mu)
    (hM : UniformContinuous fun x => fderiv ℝ Ψ (Φ x)) (hMN : ∀ x, ‖fderiv ℝ Ψ (Φ x)‖ ≤ N) :
    MemVMO (nondivPullbackPrincipal Φ Ψ A) mu := by
  have hAΦΛ : ∀ᵐ x ∂mu, ‖A (Φ x)‖ ≤ Λ :=
    ae_of_ae_map hΦ.continuous.measurable.aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul hmap).ae_le hAΛ)
  have hadj : UniformContinuous fun x => (fderiv ℝ Ψ (Φ x)).adjoint :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E)).isometry.uniformContinuous.comp hM
  -- First the product `x ↦ A(Φ x) ∘ M(x)†`, then its product with `M`.
  have h₁ : MemVMO (fun x => ContinuousLinearMap.compL ℝ E E E (A (Φ x))
      (fderiv ℝ Ψ (Φ x)).adjoint) mu :=
    (hA.comp_of_map_le_of_addHaar hΦ hmap).bilinear (ContinuousLinearMap.compL ℝ E E E) hAΦΛ
      hadj fun x => by
        rw [LinearIsometryEquiv.norm_map]
        exact hMN x
  have h₁N : ∀ᵐ x ∂mu, ‖ContinuousLinearMap.compL ℝ E E E (A (Φ x))
      (fderiv ℝ Ψ (Φ x)).adjoint‖ ≤ ((Λ * N : ℝ≥0) : ℝ) := hAΦΛ.mono fun x hx => by
    rw [ContinuousLinearMap.compL_apply, NNReal.coe_mul]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    gcongr
    exact hMN x
  have h₂ := h₁.bilinear (ContinuousLinearMap.compL ℝ E E E).flip h₁N hM hMN
  convert h₂ using 1
  funext x
  simp [nondivPullbackPrincipal_apply]

/-- **A non-divergence-form equation under a change of variables of order two.** Let `Φ` be a
change of variables of order two from `U` into `V` with inverse `Ψ`, a change of variables of order
two from `V` into `U`, and let `1 ≤ p < ∞`. If `u ∈ W^{2,p}(V)` solves

`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c₀ u = f`

almost everywhere on `V`, then `v = u ∘ Φ ∈ W^{2,p}(U)` solves

`tr (A' ∘ D²v) + ⟪b', ∇v⟫ + (c₀ ∘ Φ) v = f ∘ Φ`

almost everywhere on `U`, where, at `x ∈ U` with `y = Φ x` and `M = DΨ(y)`, `A'(x) = M ∘ A(y) ∘ M†`
and `b'(x) = M b(y) + ∑ᵢ D²Ψ(y) eᵢ (A(y)† eᵢ)` for an orthonormal basis `(eᵢ)`. The sum does not
depend on the basis, and the coefficient fields `A`, `b`, `c₀` and the right-hand side `f` are
arbitrary functions. -/
theorem ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) (hΦ : IsChangeOfVariables 2 U V Φ L c)
    (hΨ : IsChangeOfVariables 2 V U Ψ L' c') (hΦΨ : RightInvOn Ψ Φ V) (hp : p ≠ ⊤)
    (u : Wkp mu V p 2) {A : E → E →L[ℝ] E} {b : E → E} {c₀ f : E → ℝ}
    (hu : ∀ᵐ y ∂mu.restrict V, traceCLM ℝ E (A y ∘L iteratedGradient 1 u y) +
      ⟪b y, iteratedGradient 0 (lowerOrder 1 u) y⟫_ℝ + c₀ y * value 2 u y = f y) :
    ∀ᵐ x ∂mu.restrict U,
      traceCLM ℝ E ((fderiv ℝ Ψ (Φ x) ∘L A (Φ x) ∘L (fderiv ℝ Ψ (Φ x)).adjoint) ∘L
          iteratedGradient 1 (compL hΦ u) x) +
        ⟪fderiv ℝ Ψ (Φ x) (b (Φ x)) +
            ∑ i, fderiv ℝ (fderiv ℝ Ψ) (Φ x) (e i) ((A (Φ x)).adjoint (e i)),
          iteratedGradient 0 (lowerOrder 1 (compL hΦ u)) x⟫_ℝ +
        c₀ (Φ x) * value 2 (compL hΦ u) x = f (Φ x) := by
  set v := compL hΦ u
  -- `u = v ∘ Ψ`, so the chain rule along `Ψ` expresses `u` and its derivatives through `v`.
  have hvu : compL hΨ v = u := compL_compL_of_rightInvOn hΦ hΨ hΦΨ u
  have hH := inner_iteratedGradient_compL_ae hΨ hp v
  have hval := value_compL_ae hΨ v
  have hgrad : ∀ᵐ y ∂mu.restrict V, iteratedGradient 0 (lowerOrder 1 (compL hΨ v)) y =
      (fderiv ℝ Ψ y).adjoint (iteratedGradient 0 (lowerOrder 1 v) (Ψ y)) := by
    filter_upwards [gradient_firstOrder_compL_ae hΨ v] with y hy
    rw [← gradient_firstOrder_one, hy, gradient_firstOrder_one]
  rw [hvu] at hH hval hgrad
  -- The equation for `u` at `y`, rewritten in terms of `v` at `Ψ y`.
  have hkey : ∀ᵐ y ∂mu.restrict V,
      traceCLM ℝ E ((fderiv ℝ Ψ y ∘L A y ∘L (fderiv ℝ Ψ y).adjoint) ∘L
          iteratedGradient 1 v (Ψ y)) +
        ⟪fderiv ℝ Ψ y (b y) + ∑ i, fderiv ℝ (fderiv ℝ Ψ) y (e i) ((A y).adjoint (e i)),
          iteratedGradient 0 (lowerOrder 1 v) (Ψ y)⟫_ℝ +
        c₀ y * value 2 v (Ψ y) = f y := by
    filter_upwards [hu, hH, hval, hgrad] with y hy hHy hvy hgy
    rw [traceCLM_comp_eq_of_forall_inner_eq e hHy, hgy, hvy,
      ContinuousLinearMap.adjoint_inner_right] at hy
    rw [← hy, inner_add_left, sum_inner]
    ring
  filter_upwards [hΦ.ae_comp hkey, ae_restrict_mem U.isOpen.measurableSet] with x hx hxU
  rwa [hΦ.injOn (hΨ.mapsTo (hΦ.mapsTo hxU)) hxU (hΦΨ (hΦ.mapsTo hxU))] at hx

/-- **A non-divergence-form equation under a change of variables, with a right inverse of the
derivative.** Let `Φ` be a change of variables of order two from `U` into `V`, let `N(x)` be a
right inverse of `DΦ(x)` for `x ∈ U`, and let `1 ≤ p < ∞`. If `u ∈ W^{2,p}(V)` is a strong solution
of `tr (A ∘ D²u) + ⟪b, ∇u⟫ + γ u = f` almost everywhere in `V`, then `w = u ∘ Φ`
(`TauCeti.Wkp.compL`) is a strong solution of

`tr (A' ∘ D²w) + ⟪b', ∇w⟫ + γ(Φ x) w = f(Φ x)` almost everywhere in `U`,

where `A'(x) = N(x) A(Φ x) N(x)†` and, for any orthonormal basis `(eᵢ)` of `E`,
`b'(x) = N(x) (b(Φ x) - ∑ᵢ D²Φ(x) eᵢ (N(x) A(Φ x)† N(x)† eᵢ))`; note `A'(x)† = N(x) A(Φ x)† N(x)†`.
Unlike `TauCeti.PDE.ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq`, no inverse
change of variables is needed. -/
theorem ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq_of_fderiv_comp_eq_id
    (h : IsChangeOfVariables 2 U V Φ L c) (hp : p ≠ ⊤) {N : E → E →L[ℝ] E}
    (hN : ∀ x ∈ (U : Set E), fderiv ℝ Φ x ∘L N x = ContinuousLinearMap.id ℝ E)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E)
    {A : E → E →L[ℝ] E} {b : E → E} {γ f : E → ℝ} {u : Wkp mu V p 2}
    (hu : ∀ᵐ y ∂mu.restrict V, traceCLM ℝ E (A y ∘L iteratedGradient 1 u y) +
      ⟪b y, iteratedGradient 0 (lowerOrder 1 u) y⟫_ℝ + γ y * value 2 u y = f y) :
    ∀ᵐ x ∂mu.restrict U,
      traceCLM ℝ E ((N x ∘L A (Φ x) ∘L (N x).adjoint) ∘L iteratedGradient 1 (compL h u) x) +
        ⟪N x (b (Φ x) - ∑ i, fderiv ℝ (fderiv ℝ Φ) x (e i)
            (N x ((A (Φ x)).adjoint ((N x).adjoint (e i))))),
          iteratedGradient 0 (lowerOrder 1 (compL h u)) x⟫_ℝ +
        γ (Φ x) * value 2 (compL h u) x = f (Φ x) := by
  filter_upwards [h.ae_comp hu, inner_iteratedGradient_compL_ae h hp u,
    gradient_firstOrder_compL_ae h u, value_compL_ae h u,
    ae_restrict_mem U.isOpen.measurableSet] with x hux hD hg hv hx
  rw [← gradient_firstOrder_one, hg, gradient_firstOrder_one]
  set M := fderiv ℝ Φ x
  set g := iteratedGradient 0 (lowerOrder 1 u) (Φ x)
  set A' := N x ∘L A (Φ x) ∘L (N x).adjoint with hA'def
  have hMN := hN x hx
  have hA' : ∀ z, A'.adjoint z = N x ((A (Φ x)).adjoint ((N x).adjoint z)) := fun z => by
    simp [A', ContinuousLinearMap.adjoint_comp]
  -- The trace of `A' ∘ D²w`, computed on the basis `e`.
  have htr : traceCLM ℝ E (A' ∘L iteratedGradient 1 (compL h u) x) =
      traceCLM ℝ E (A (Φ x) ∘L iteratedGradient 1 u (Φ x)) +
        ⟪∑ i, fderiv ℝ (fderiv ℝ Φ) x (e i) (A'.adjoint (e i)), g⟫_ℝ := by
    have hH (f : E) : (iteratedGradient 1 (compL h u) x -
        M.adjoint ∘L iteratedGradient 1 u (Φ x) ∘L M) f =
          (fderiv ℝ (fderiv ℝ Φ) x f).adjoint g := by
      refine ext_inner_right ℝ fun f' => ?_
      rw [sub_apply, inner_sub_left, hD f f', ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_left, add_sub_cancel_left]
    rw [← sub_add_cancel (iteratedGradient 1 (compL h u) x)
        (M.adjoint ∘L iteratedGradient 1 u (Φ x) ∘L M), ContinuousLinearMap.comp_add,
      map_add, hA'def, ContinuousLinearMap.traceCLM_comp_adjoint_comp_comp_of_comp_eq_id hMN,
      ContinuousLinearMap.traceCLM_comp_eq_sum_inner _ e _ g hH, add_comm]
  -- The drift: `⟪N z, M† g⟫ = ⟪z, g⟫` since `M N = 1`.
  have hdrift (z : E) : ⟪N x z, M.adjoint g⟫_ℝ = ⟪z, g⟫_ℝ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    simpa using congrArg (fun z' => ⟪z', g⟫_ℝ) (congrArg (fun T => T z) hMN)
  rw [htr, hv, hdrift, ← hux]
  simp only [hA', inner_sub_left]
  ring

/-- **The pulled-back equation in terms of `nondivPullbackPrincipal` and `nondivPullbackDrift`.**
If `u ∈ W^{2,p}(V)` solves `tr (A ∘ D²u) + ⟪b, ∇u⟫ + c₀ u = f` almost everywhere on `V`, then
`u ∘ Φ` solves the equation with coefficients `nondivPullbackPrincipal Φ Ψ A`,
`nondivPullbackDrift Φ Ψ A b` and `c₀ ∘ Φ` and right-hand side `f ∘ Φ` almost everywhere on `U`.
This is `TauCeti.PDE.ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq` for the
standard orthonormal basis. -/
theorem ae_traceCLM_nondivPullbackPrincipal_comp_add_inner_nondivPullbackDrift_add_mul_eq
    (hΦ : IsChangeOfVariables 2 U V Φ L c) (hΨ : IsChangeOfVariables 2 V U Ψ L' c')
    (hΦΨ : RightInvOn Ψ Φ V) (hp : p ≠ ⊤) (u : Wkp mu V p 2) {A : E → E →L[ℝ] E} {b : E → E}
    {c₀ f : E → ℝ}
    (hu : ∀ᵐ y ∂mu.restrict V, traceCLM ℝ E (A y ∘L iteratedGradient 1 u y) +
      ⟪b y, iteratedGradient 0 (lowerOrder 1 u) y⟫_ℝ + c₀ y * value 2 u y = f y) :
    ∀ᵐ x ∂mu.restrict U,
      traceCLM ℝ E (nondivPullbackPrincipal Φ Ψ A x ∘L iteratedGradient 1 (compL hΦ u) x) +
        ⟪nondivPullbackDrift Φ Ψ A b x, iteratedGradient 0 (lowerOrder 1 (compL hΦ u)) x⟫_ℝ +
        c₀ (Φ x) * value 2 (compL hΦ u) x = f (Φ x) := by
  filter_upwards [ae_traceCLM_comp_iteratedGradient_compL_add_inner_add_mul_eq
    (stdOrthonormalBasis ℝ E) hΦ hΨ hΦΨ hp u hu] with x hx
  simpa only [nondivPullbackPrincipal_apply, nondivPullbackDrift_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val] using hx

end TauCeti.PDE
