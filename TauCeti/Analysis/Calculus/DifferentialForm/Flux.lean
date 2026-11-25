/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Coordinates
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
public import TauCeti.MeasureTheory.Integral.DivergenceTheorem.Affine
import Mathlib.Analysis.Calculus.FDeriv.Pi
import TauCeti.Topology.Algebra.Module.Alternating.Topology

/-!
# Coordinate flux forms, exterior divergence, and affine cofactor pullback

On the coordinate space `Fin (n + 1) → ℝ`, a family of vector-valued components
`F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E` determines the *flux `n`-form*

`fluxForm F x = ∑ i, (-1)^i F i x dx₀ ∧ ⋯ ∧ dx̂ᵢ ∧ ⋯ ∧ dxₙ`,

built from the coordinate `(n × n)` minor forms `coordMinorForm i` from
`TauCeti.Analysis.Calculus.DifferentialForm.Coordinates`. On the standard coordinate `n`-tuple
omitting `eⱼ`, `fluxForm F x` evaluates to `(-1)^j • F j x`, so its signed omission coefficients
(`ContinuousAlternatingMap.signedRemoveNth`) are literally `j ↦ F j x`. Consequently, whenever
every `F i` is differentiable at `x`, the exterior derivative of `fluxForm F` at `x` is the
divergence times the standard volume `(n + 1)`-form `(Pi.basisFun ℝ (Fin (n + 1))).continuousDet`:
`(Pi.basisFun ℝ (Fin (n + 1))).continuousDet.smulRight (∑ i, fderiv ℝ (F i) x (Pi.single i 1))`.

Under an invertible affine map `u ↦ p + L u` with `L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)`,
three-column Laplace/cofactor expansion of `coordMinorForm` identifies the linear pullback of
`fluxForm F (p + L u)` along `L` with `fluxForm (L.affineFluxPullback p F) u`, with no regularity
assumptions on `F`. Consuming Mathlib's `extDeriv_pullback` along the smooth affine map
`u ↦ p + L u` then yields the exterior derivative of the pulled-back flux form at any point `u`
where each `F i` is merely differentiable at `p + L u`.

## Main declarations

* `TauCeti.fluxForm`: the `E`-valued flux `n`-form `∑ i, (-1)^i F i dx₀ ∧ ⋯ ∧ dx̂ᵢ ∧ ⋯ ∧ dxₙ`.
* `TauCeti.differentiableAt_fluxForm_iff`: `fluxForm F` is differentiable at `x` iff every
  component `F i` is differentiable at `x`.
* `TauCeti.extDerivWithin_fluxForm`, `TauCeti.extDeriv_fluxForm`: exterior derivative of
  `fluxForm F` as divergence times `(Pi.basisFun ℝ (Fin (n + 1))).continuousDet`.
* `ContinuousLinearEquiv.fluxForm_comp_affine`: affine pullback of `fluxForm F` equals
  `fluxForm (L.affineFluxPullback p F)`.
* `ContinuousLinearEquiv.extDeriv_fluxForm_affineFluxPullback`: exterior derivative of the
  affine-pulled-back flux form via `extDeriv_pullback`.

## References

* M. Spivak, *Calculus on Manifolds*, Chapter 4 (coordinate differential forms and Stokes' theorem).
* P. G. Ciarlet, *Mathematical Elasticity, Vol. I*, North-Holland (1988), §1.7 (Piola / cofactor
  transform of flux fields).
-/

public section

noncomputable section

open Set

namespace TauCeti

section FluxForm

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `E`-valued flux `n`-form `∑ i, (-1)^i F i x dx₀ ∧ ⋯ ∧ dx̂ᵢ ∧ ⋯ ∧ dxₙ` associated to a
coordinate field family `F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E`. -/
def fluxForm (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) (x : Fin (n + 1) → ℝ) :
    (Fin (n + 1) → ℝ) [⋀^Fin n]→L[ℝ] E :=
  ∑ i : Fin (n + 1), (coordMinorForm i).smulRight ((-1 : ℝ) ^ (i : ℕ) • F i x)

theorem fluxForm_apply (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) (x : Fin (n + 1) → ℝ)
    (v : Fin n → Fin (n + 1) → ℝ) :
    fluxForm F x v = ∑ i : Fin (n + 1), ((-1 : ℝ) ^ (i : ℕ) * coordMinorForm i v) • F i x := by
  simp only [fluxForm, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smulRight_apply, mul_comm _ (coordMinorForm _ v), mul_smul]

private theorem fluxForm_eq_sum_clm (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E)
    (x : Fin (n + 1) → ℝ) :
    fluxForm F x =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) • (coordMinorForm i).smulRightCLM (F i x) := by
  simp only [fluxForm, ← ContinuousAlternatingMap.smulRightCLM_apply, map_smul]

@[simp]
theorem fluxForm_removeNth_single (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E)
    (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    fluxForm F x (j.removeNth fun k : Fin (n + 1) ↦ (Pi.single k 1 : Fin (n + 1) → ℝ)) =
      (-1 : ℝ) ^ (j : ℕ) • F j x := by
  simp [fluxForm_apply]

/-- The signed coordinate-omission evaluations of `fluxForm F x` recover the field components
`j ↦ F j x`. -/
@[simp]
theorem signedRemoveNth_fluxForm (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E)
    (x : Fin (n + 1) → ℝ) :
    ContinuousAlternatingMap.signedRemoveNth
      (fun k : Fin (n + 1) ↦ (Pi.single k 1 : Fin (n + 1) → ℝ)) (fluxForm F x) =
      fun j ↦ F j x := by
  ext j
  rw [ContinuousAlternatingMap.signedRemoveNth_apply, fluxForm_removeNth_single, smul_smul,
    ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- If every component field `F i` is continuous on `s`, then the flux form `fluxForm F` is
continuous on `s`. -/
theorem continuousOn_fluxForm {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {s : Set (Fin (n + 1) → ℝ)} (hF : ∀ i, ContinuousOn (F i) s) :
    ContinuousOn (fluxForm F) s := by
  rw [funext (fluxForm_eq_sum_clm F)]
  refine continuousOn_finsetSum _ fun i _ ↦ ?_
  exact (continuousOn_const (c := (-1 : ℝ) ^ (i : ℕ))).smul
    (((coordMinorForm i).smulRightCLM (F := E)).continuous.comp_continuousOn (hF i))

/-- If every component field `F i` is differentiable within `s` at `x`, then `fluxForm F` is
differentiable within `s` at `x`. -/
theorem differentiableWithinAt_fluxForm {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {s : Set (Fin (n + 1) → ℝ)} {x : Fin (n + 1) → ℝ}
    (hF : ∀ i, DifferentiableWithinAt ℝ (F i) s x) :
    DifferentiableWithinAt ℝ (fluxForm F) s x := by
  rw [funext (fluxForm_eq_sum_clm F)]
  refine DifferentiableWithinAt.fun_sum fun i _ ↦ ?_
  exact (((coordMinorForm i).smulRightCLM (F := E)).differentiableAt.comp_differentiableWithinAt x
    (hF i)).const_smul ((-1 : ℝ) ^ (i : ℕ))

/-- If every component field `F i` is differentiable at `x`, then `fluxForm F` is differentiable
at `x`. -/
theorem differentiableAt_fluxForm {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {x : Fin (n + 1) → ℝ} (hF : ∀ i, DifferentiableAt ℝ (F i) x) :
    DifferentiableAt ℝ (fluxForm F) x := by
  rw [← differentiableWithinAt_univ]
  exact differentiableWithinAt_fluxForm fun i ↦ (hF i).differentiableWithinAt

/-- The flux form `fluxForm F` is differentiable at `x` if and only if every component field `F i`
is differentiable at `x`: the continuous linear omission map `signedRemoveNth` recovers the
component fields from the form. -/
theorem differentiableAt_fluxForm_iff {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {x : Fin (n + 1) → ℝ} :
    DifferentiableAt ℝ (fluxForm F) x ↔ ∀ i, DifferentiableAt ℝ (F i) x := by
  refine ⟨fun hd ↦ ?_, differentiableAt_fluxForm⟩
  let e : Fin (n + 1) → Fin (n + 1) → ℝ := fun k ↦ Pi.single k 1
  have hcomp : DifferentiableAt ℝ
      (ContinuousAlternatingMap.signedRemoveNth (𝕜 := ℝ) (F := E) e ∘ fluxForm F) x :=
    ((ContinuousAlternatingMap.signedRemoveNth (𝕜 := ℝ) (F := E) e).differentiableAt.comp x hd)
  have heq : ContinuousAlternatingMap.signedRemoveNth (𝕜 := ℝ) (F := E) e ∘ fluxForm F =
      fun y i ↦ F i y := funext fun y ↦ signedRemoveNth_fluxForm F y
  exact differentiableAt_pi.mp (heq ▸ hcomp)

/-- If every component field `F i` is `C^r` on `s`, then `fluxForm F` is `C^r` on `s`. -/
theorem contDiffOn_fluxForm {r : WithTop ℕ∞} {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {s : Set (Fin (n + 1) → ℝ)} (hF : ∀ i, ContDiffOn ℝ r (F i) s) :
    ContDiffOn ℝ r (fluxForm F) s := by
  rw [funext (fluxForm_eq_sum_clm F)]
  refine ContDiffOn.sum fun i _ ↦ ?_
  exact (((coordMinorForm i).smulRightCLM (F := E)).contDiff.comp_contDiffOn (hF i)).const_smul
    ((-1 : ℝ) ^ (i : ℕ))

/-- If every component field `F i` is globally `C^r`, then `fluxForm F` is globally `C^r`. -/
theorem contDiff_fluxForm {r : WithTop ℕ∞} {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    (hF : ∀ i, ContDiff ℝ r (F i)) :
    ContDiff ℝ r (fluxForm F) := by
  rw [funext (fluxForm_eq_sum_clm F)]
  refine ContDiff.sum fun i _ ↦ ?_
  exact (((coordMinorForm i).smulRightCLM (F := E)).contDiff.comp (hF i)).const_smul
    ((-1 : ℝ) ^ (i : ℕ))

/-- Evaluated on the standard coordinate frame, the within-set exterior derivative of `fluxForm F`
is the divergence `∑ i, ∂ᵢ (F i)`. -/
theorem extDerivWithin_fluxForm_apply_single {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {s : Set (Fin (n + 1) → ℝ)} {x : Fin (n + 1) → ℝ} (hs : UniqueDiffWithinAt ℝ s x)
    (hF : ∀ i, DifferentiableWithinAt ℝ (F i) s x) :
    extDerivWithin (fluxForm F) s x (fun i ↦ Pi.single i 1) =
      ∑ i : Fin (n + 1), fderivWithin ℝ (F i) s x (Pi.single i 1) := by
  let e : Fin (n + 1) → Fin (n + 1) → ℝ := fun i ↦ Pi.single i 1
  have hsum := (differentiableWithinAt_fluxForm hF).sum_fderivWithin_signedRemoveNth hs e
  have hcomp : ContinuousAlternatingMap.signedRemoveNth (𝕜 := ℝ) (F := E) e ∘ fluxForm F =
      fun y i ↦ F i y := funext fun y ↦ signedRemoveNth_fluxForm F y
  rw [← hsum, hcomp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderivWithin_pi hF hs, ContinuousLinearMap.pi_apply]

/-- Within a set of unique differentiability, the exterior derivative of `fluxForm F` is the
divergence tensored with `(Pi.basisFun ℝ (Fin (n + 1))).continuousDet`. -/
theorem extDerivWithin_fluxForm {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {s : Set (Fin (n + 1) → ℝ)} {x : Fin (n + 1) → ℝ} (hs : UniqueDiffWithinAt ℝ s x)
    (hF : ∀ i, DifferentiableWithinAt ℝ (F i) s x) :
    extDerivWithin (fluxForm F) s x =
      (Pi.basisFun ℝ (Fin (n + 1))).continuousDet.smulRight
        (∑ i : Fin (n + 1), fderivWithin ℝ (F i) s x (Pi.single i 1)) := by
  rw [(extDerivWithin (fluxForm F) s x).eq_continuousDet_smulRight (Pi.basisFun ℝ (Fin (n + 1))),
    funext (Pi.basisFun_apply ℝ (Fin (n + 1))), extDerivWithin_fluxForm_apply_single hs hF]

/-- Evaluated on the standard coordinate frame, the exterior derivative of `fluxForm F` at `x` is
the divergence `∑ i, ∂ᵢ (F i) x`. Only differentiability at `x` is required. -/
theorem extDeriv_fluxForm_apply_single {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {x : Fin (n + 1) → ℝ} (hF : ∀ i, DifferentiableAt ℝ (F i) x) :
    extDeriv (fluxForm F) x (fun i ↦ Pi.single i 1) =
      ∑ i : Fin (n + 1), fderiv ℝ (F i) x (Pi.single i 1) := by
  simpa only [extDerivWithin_univ, fderivWithin_univ] using
    extDerivWithin_fluxForm_apply_single uniqueDiffWithinAt_univ
      fun i ↦ (hF i).differentiableWithinAt

/-- The exterior derivative of `fluxForm F` at `x` equals the divergence tensored with
`(Pi.basisFun ℝ (Fin (n + 1))).continuousDet`. Only differentiability of each component at `x` is
required. -/
theorem extDeriv_fluxForm {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {x : Fin (n + 1) → ℝ} (hF : ∀ i, DifferentiableAt ℝ (F i) x) :
    extDeriv (fluxForm F) x =
      (Pi.basisFun ℝ (Fin (n + 1))).continuousDet.smulRight
        (∑ i : Fin (n + 1), fderiv ℝ (F i) x (Pi.single i 1)) := by
  simpa only [extDerivWithin_univ, fderivWithin_univ] using
    extDerivWithin_fluxForm uniqueDiffWithinAt_univ fun i ↦ (hF i).differentiableWithinAt

end FluxForm

end TauCeti

namespace ContinuousLinearEquiv

open TauCeti

variable {n : ℕ} (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))

/-- Under an invertible linear change of tangent coordinates, each signed `n × n` coordinate minor
expands in the parameter coordinate minors with the cofactor matrix `det L • L⁻¹`. -/
theorem signed_coordMinorForm_map (i : Fin (n + 1)) (v : Fin n → Fin (n + 1) → ℝ) :
    (-1 : ℝ) ^ (i : ℕ) * coordMinorForm i (fun r ↦ L (v r)) =
      LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ) *
        ∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * L.symm (Pi.single i 1) j * coordMinorForm j v := by
  have hlhs := sum_signed_mul_coordMinorForm (Pi.single i (1 : ℝ)) (fun r ↦ L (v r))
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hlhs
  rw [hlhs, ← Pi.basisFun_det_apply]
  have hdet := (Pi.basisFun ℝ (Fin (n + 1))).det_comp L.toLinearMap
    (Fin.cons (L.symm (Pi.single i 1)) v)
  have hcons : (L.toLinearMap ∘ Fin.cons (L.symm (Pi.single i 1)) v) =
      Fin.cons (Pi.single i 1) (fun r ↦ L (v r)) := by
    ext k
    refine Fin.cases ?_ (fun r ↦ ?_) k <;> simp
  rw [← hcons, hdet, Pi.basisFun_det_apply, ← sum_signed_mul_coordMinorForm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : Fin (n + 1) → ℝ)

/-- Pulling `fluxForm F (p + L u)` back along `L` produces the flux form of the cofactor pullback
`L.affineFluxPullback p F` at `u`, with no regularity hypotheses on `F`. -/
theorem fluxForm_comp_affine (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E) (u : Fin (n + 1) → ℝ) :
    (fluxForm F (p + L u)).compContinuousLinearMap L.toContinuousLinearMap =
      fluxForm (L.affineFluxPullback p F) u := by
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, fluxForm_apply, fluxForm_apply]
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe, L.signed_coordMinorForm_map,
    L.affineFluxPullback_apply, Finset.mul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_smul]
  congr 1
  ring

/-- By `extDeriv_pullback` along the smooth affine map `u ↦ p + L u`, the exterior derivative of
`fluxForm (L.affineFluxPullback p F)` at `u` equals the signed determinant times the divergence of
`F` at `p + L u` tensored with `(Pi.basisFun ℝ (Fin (n + 1))).continuousDet`. Only differentiability
of each `F i` at `p + L u` is required. -/
theorem extDeriv_fluxForm_affineFluxPullback {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E}
    {u : Fin (n + 1) → ℝ} (hF : ∀ i, DifferentiableAt ℝ (F i) (p + L u)) :
    extDeriv (fluxForm (L.affineFluxPullback p F)) u =
      (Pi.basisFun ℝ (Fin (n + 1))).continuousDet.smulRight
        (LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ) •
          ∑ i : Fin (n + 1), fderiv ℝ (F i) (p + L u) (Pi.single i 1)) := by
  let A : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun w ↦ p + L w
  have hfderiv (w : Fin (n + 1) → ℝ) : fderiv ℝ A w = L.toContinuousLinearMap :=
    (L.toContinuousLinearMap.hasFDerivAt.const_add p).fderiv
  have hA : ContDiffAt ℝ (2 : WithTop ℕ∞) A u :=
    (contDiff_const.add L.toContinuousLinearMap.contDiff).contDiffAt
  have hpull : fluxForm (L.affineFluxPullback p F) =
      fun w ↦ (fluxForm F (A w)).compContinuousLinearMap (fderiv ℝ A w) := by
    funext w
    rw [hfderiv w, L.fluxForm_comp_affine p F w]
  have hd : DifferentiableAt ℝ (fluxForm F) (A u) := differentiableAt_fluxForm hF
  rw [hpull, extDeriv_pullback (f := A) hd hA (by norm_num), hfderiv u, extDeriv_fluxForm hF]
  ext v
  have hv := congrArg (· v)
    ((Pi.basisFun ℝ (Fin (n + 1))).continuousDet_compContinuousLinearMap L.toContinuousLinearMap)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousLinearEquiv.coe_coe, smul_eq_mul] at hv ⊢
  simp only [ContinuousAlternatingMap.smulRight_apply]
  rw [hv, mul_comm, mul_smul, ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap]

/-- Evaluated on the standard coordinate frame, the exterior derivative of
`fluxForm (L.affineFluxPullback p F)` at `u` is `det L` times the divergence of `F` at `p + L u`. -/
theorem extDeriv_fluxForm_affineFluxPullback_apply_single
    {F : Fin (n + 1) → (Fin (n + 1) → ℝ) → E} {u : Fin (n + 1) → ℝ}
    (hF : ∀ i, DifferentiableAt ℝ (F i) (p + L u)) :
    extDeriv (fluxForm (L.affineFluxPullback p F)) u (fun i ↦ Pi.single i 1) =
      LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ) •
        ∑ i : Fin (n + 1), fderiv ℝ (F i) (p + L u) (Pi.single i 1) := by
  rw [L.extDeriv_fluxForm_affineFluxPullback p hF, ContinuousAlternatingMap.smulRight_apply,
    ← funext (Pi.basisFun_apply ℝ (Fin (n + 1))), Module.Basis.continuousDet_apply,
    Module.Basis.det_self, one_smul]

end ContinuousLinearEquiv

end
