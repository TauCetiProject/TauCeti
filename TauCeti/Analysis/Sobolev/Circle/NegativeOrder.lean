/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Diffeomorphism
public import TauCeti.Analysis.Sobolev.Circle.Duality
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.Deriv.AddCircle
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Circle diffeomorphisms act on the Sobolev spaces of negative order

A fixed diffeomorphism `φ` of the circle should induce a bounded isomorphism `u ↦ u ∘ φ` of every
Sobolev space `H^s`, `s` real, so that these spaces do not depend on the parametrization of the
circle. `TauCeti/Analysis/Sobolev/Circle/Diffeomorphism.lean` treats the orders `s ≥ 0`, where
`u ∘ φ` is precomposition of square-integrable functions. This file treats the orders `t ≤ 0`,
where an element of `H^t` is in general not a function, and `u ∘ φ` is defined by duality.

Let `φ` have the lift `F`, `F (x + T) = F x + T`, with smooth derivative `0 < c ≤ F' ≤ M`. The
change of variables `y = φ x` shows that the `L²` adjoint of precomposition with `φ` is
`v ↦ (v / F') ∘ φ⁻¹` (`TauCeti.CircleSobolev.adjoint_precompEquivOfLift`). Division by the smooth
function `F'` and precomposition with `φ⁻¹` both preserve `H^(-t)`, `-t ≥ 0`, so this adjoint
restricts to an automorphism `Q` of the Hilbert space `H^(-t)`. The space `H^t` is identified with
`H^(-t)` by the isometry `TauCeti.CircleSobolev.weightEquiv`, under which the inner product of
`H^(-t)` becomes the `L²` pairing of `H^t` with `H^(-t)`. Transporting the Hilbert adjoint of `Q`
along this isometry gives an automorphism of `H^t`
(`TauCeti.CircleSobolev.precompNonposEquivOfLift`). On the dense subspace `H⁰` of `H^t` it is
precomposition with `φ` (`TauCeti.CircleSobolev.precompNonposEquivOfLift_inclusion`), which
determines it.

## Main definitions

* `TauCeti.CircleSobolev.precompNonposEquivOfLift`: for `t ≤ 0` and `φ` with lift `F` and smooth
  derivative `0 < c ≤ F' ≤ M`, the continuous linear automorphism `u ↦ u ∘ φ` of `H^t`.

## Main statements

* `TauCeti.CircleSobolev.adjoint_precompEquivOfLift`: the `L²` adjoint of `u ↦ u ∘ φ` is
  `v ↦ (v / F') ∘ φ⁻¹`.
* `TauCeti.CircleSobolev.precompNonposEquivOfLift_inclusion`: on elements of `H⁰` it is the
  precomposition `TauCeti.CircleSobolev.precompEquivOfLift`; similarly for its inverse
  (`TauCeti.CircleSobolev.precompNonposEquivOfLift_symm_inclusion`).
* `TauCeti.CircleSobolev.inclusion_precompNonposEquivOfLift_of_le` and
  `TauCeti.CircleSobolev.inclusion_precompSmoothEquivOfLift_of_nonpos`: the operators on all the
  real orders are compatible with the inclusions `H^s → H^t`, `t ≤ s`.
* `TauCeti.CircleSobolev.precompNonposEquivOfLift_symm_eq`: the inverse is precomposition with the
  inverse map of the circle, presented by any of its smooth lifts.

## References

* M. E. Taylor, *Partial Differential Equations I*, Chapter 4, §1 (Sobolev spaces of negative
  order on the torus as duals, and their invariance under diffeomorphisms).
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the Sobolev spaces of boundary maps on which
  the Hardy decompositions of cut Riemann surfaces are carried out.
-/

public section

noncomputable section

open MeasureTheory AddCircle Complex
open scoped ContDiff

namespace TauCeti

namespace CircleSobolev

variable {T : ℝ} [hT : Fact (0 < T)] {φ : AddCircle T → AddCircle T}

section Lift

variable {F F' : ℝ → ℝ} {c M : ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
  (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x) (hc : 0 < c)
  (hcF : ∀ x, c ≤ F' x) (hMF : ∀ x, F' x ≤ M) (hF' : ContDiff ℝ ∞ F')

include hF' in
/-- **The `L²` adjoint of precomposition with a circle diffeomorphism.** Let `φ` have the lift `F`
with smooth derivative `0 < c ≤ F' ≤ M`, and let `f'` be `F'` regarded as a function on the
circle. The adjoint of `u ↦ u ∘ φ` on `H⁰ = L²` is `v ↦ (v / f') ∘ φ⁻¹`: by the change of variables
`y = φ x`, `∫ conj (v y) (u (φ y)) dy = ∫ conj ((v / f') (φ⁻¹ y)) u y dy`. -/
theorem adjoint_precompEquivOfLift {f' : AddCircle T → ℂ} (hf' : ∀ x : ℝ, f' x = F' x) :
    ContinuousLinearMap.adjoint
        (precompEquivOfLift hF hper hφ hc hcF hMF : CircleSobolev 0 ℂ →L[ℂ] CircleSobolev 0 ℂ) =
      ((precompEquivOfLift hF hper hφ hc hcF hMF).symm :
          CircleSobolev 0 ℂ →L[ℂ] CircleSobolev 0 ℂ) ∘L
        mulFourierSeries (fourierCoeff fun x ↦ (f' x)⁻¹) := by
  set P := precompEquivOfLift hF hper hφ hc hcF hMF
  -- `f'` is the derivative of the lift, regarded as a function on the circle.
  obtain rfl : f' = derivOfLift hF hper hF'.continuous := funext fun y ↦ by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [hf', derivOfLift_coe]
  have hf'₀ := derivOfLift_ne_zero hF hper hc hcF hF'.continuous
  -- On `H⁰`, multiplication by the smooth function `1 / f'` is the multiplication operator.
  have hinv := (contDiff_derivOfLift hF hper hF' hF'.continuous).inv fun x ↦ hf'₀ x
  let g : C(AddCircle T, ℂ) :=
    ⟨fun x ↦ (derivOfLift hF hper hF'.continuous x)⁻¹, (map_continuous _).inv₀ hf'₀⟩
  have hM : (mulFourierSeries (fourierCoeff fun x ↦ (derivOfLift hF hper hF'.continuous x)⁻¹) :
      CircleSobolev 0 ℂ →L[ℂ] CircleSobolev 0 ℂ) =
        multiplicationOperator (ContinuousMap.toLp ⊤ haarAddCircle ℂ g) :=
    mulFourierSeries_fourierCoeff_eq_multiplicationOperator (f := g) hinv
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun a b ↦ ?_).symm
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  set v := P.symm (mulFourierSeries
    (fourierCoeff fun x ↦ (derivOfLift hF hper hF'.continuous x)⁻¹) a)
  have hv : P v = multiplicationOperator (ContinuousMap.toLp ⊤ haarAddCircle ℂ g) a := by
    rw [ContinuousLinearEquiv.apply_symm_apply, hM]
  -- Change variables `y = φ x` in the `L²` inner product of `v` and `b`.
  rw [← (toLpₗᵢ T).inner_map_map v b, ← (toLpₗᵢ T).inner_map_map a (P b), L2.inner_def,
    L2.inner_def, ← integral_haarAddCircle_deriv_smul_comp_of_lift hF hper hφ
      (fun x ↦ (hc.trans_le (hcF x)).le) (f' := (periodic_deriv_of_lift hF hper).lift)
      (fun _ ↦ rfl)
      (fun y ↦ inner ℂ (toLpₗᵢ T v y) (toLpₗᵢ T b y))]
  refine integral_congr_ae ?_
  filter_upwards [toLpₗᵢ_precompEquivOfLift hF hper hφ hc hcF hMF v,
    toLpₗᵢ_precompEquivOfLift hF hper hφ hc hcF hMF b,
    toLpₗᵢ_multiplicationOperator_ae (ContinuousMap.toLp ⊤ haarAddCircle ℂ g) a,
    ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ) haarAddCircle g] with x h₁ h₂ h₃ h₄
  rw [hv] at h₁
  rw [← Function.comp_apply (f := toLpₗᵢ T v), ← h₁, ← Function.comp_apply (f := toLpₗᵢ T b), ← h₂,
    h₃, h₄]
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hy := hf'₀ y
  rw [derivOfLift_coe] at hy
  simp [g, P, Function.Periodic.lift_coe]
  field_simp

/-- The `L²` adjoint `v ↦ (v / F') ∘ φ⁻¹` of precomposition with `φ`, as an automorphism of `H^s`,
`s ≥ 0`. -/
private def adjointEquiv {s : ℝ} (hs : 0 ≤ s) : CircleSobolev s ℂ ≃L[ℂ] CircleSobolev s ℂ :=
  (mulFourierSeriesEquiv (derivOfLift hF hper hF'.continuous)
    (contDiff_derivOfLift hF hper hF' _) (derivOfLift_ne_zero hF hper hc hcF _)).symm.trans
    (precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' hs).symm

/-- In `H⁰`, `adjointEquiv` is the `L²` adjoint of precomposition with `φ`. -/
private theorem inclusion_adjointEquiv {s : ℝ} (hs : 0 ≤ s) (a : CircleSobolev s ℂ) :
    inclusion hs (adjointEquiv hF hper hφ hc hcF hMF hF' hs a) =
      ContinuousLinearMap.adjoint
        (precompEquivOfLift hF hper hφ hc hcF hMF : CircleSobolev 0 ℂ →L[ℂ] CircleSobolev 0 ℂ)
        (inclusion hs a) := by
  have hsum := summable_weight_mul_norm_fourierCoeff_of_contDiff
    (f := fun y ↦ (derivOfLift hF hper hF'.continuous y)⁻¹)
    ((contDiff_derivOfLift hF hper hF' _).inv fun x ↦ derivOfLift_ne_zero hF hper hc hcF _ x)
  rw [adjoint_precompEquivOfLift hF hper hφ hc hcF hMF hF' (derivOfLift_coe hF hper _),
    adjointEquiv, ContinuousLinearEquiv.trans_apply, inclusion_precompSmoothEquivOfLift_symm,
    coe_mulFourierSeriesEquiv_symm, inclusion_mulFourierSeries hs (hsum _) (hsum _),
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

/-- **Smooth circle diffeomorphisms act on `H^t`, `t ≤ 0`.** Let `φ` be the map of the circle with
lift `F`, so that `F (x + T) = F x + T` and `φ x = F x`, and suppose that `F` has a smooth
derivative with `0 < c ≤ F' ≤ M`. Then for every real `t ≤ 0`, `u ↦ u ∘ φ` is a continuous linear
automorphism of `H^t`. It is defined by duality with `H^(-t)`: under the isometry
`weightEquiv t (-t)` it is the Hilbert adjoint on `H^(-t)` of `v ↦ (v / F') ∘ φ⁻¹`. On elements of
`H⁰` it is precomposition with `φ` (`TauCeti.CircleSobolev.precompNonposEquivOfLift_inclusion`),
and its inverse is precomposition with the inverse map of the circle
(`TauCeti.CircleSobolev.precompNonposEquivOfLift_symm_eq`). -/
def precompNonposEquivOfLift {t : ℝ} (ht : t ≤ 0) : CircleSobolev t ℂ ≃L[ℂ] CircleSobolev t ℂ :=
  let Q := adjointEquiv hF hper hφ hc hcF hMF hF' (neg_nonneg.2 ht)
  (weightEquiv t (-t) ℂ).toContinuousLinearEquiv.trans
    (Q.adjointEquiv.trans (weightEquiv t (-t) ℂ).toContinuousLinearEquiv.symm)

/-- The defining formula of `precompNonposEquivOfLift`. -/
private theorem weightEquiv_precompNonposEquivOfLift {t : ℝ} (ht : t ≤ 0) (a : CircleSobolev t ℂ) :
    weightEquiv t (-t) ℂ (precompNonposEquivOfLift hF hper hφ hc hcF hMF hF' ht a) =
      ContinuousLinearMap.adjoint
        (adjointEquiv hF hper hφ hc hcF hMF hF' (neg_nonneg.2 ht) :
          CircleSobolev (-t) ℂ →L[ℂ] CircleSobolev (-t) ℂ) (weightEquiv t (-t) ℂ a) := by
  simp [precompNonposEquivOfLift]

/-- **Precomposition on `H^t`, `t ≤ 0`, extends precomposition on `H⁰`.** For `u ∈ H⁰`, the
element `u ∘ φ` of `H^t` is the image of the element `u ∘ φ` of `H⁰`. -/
@[simp]
theorem precompNonposEquivOfLift_inclusion {t : ℝ} (ht : t ≤ 0) (a : CircleSobolev 0 ℂ) :
    precompNonposEquivOfLift hF hper hφ hc hcF hMF hF' ht (inclusion ht a) =
      inclusion ht (precompEquivOfLift hF hper hφ hc hcF hMF a) := by
  refine (weightEquiv t (-t) ℂ).injective (ext_inner_right ℂ fun b ↦ ?_)
  rw [weightEquiv_precompNonposEquivOfLift, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearEquiv.coe_coe, inner_weightEquiv_inclusion, inclusion_adjointEquiv,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearEquiv.coe_coe,
    inner_weightEquiv_inclusion]

/-- For `u ∈ H⁰`, the inverse of precomposition on `H^t`, `t ≤ 0`, sends `u` to the image of the
inverse precomposition of `u` in `H⁰`. -/
@[simp]
theorem precompNonposEquivOfLift_symm_inclusion {t : ℝ} (ht : t ≤ 0) (a : CircleSobolev 0 ℂ) :
    (precompNonposEquivOfLift hF hper hφ hc hcF hMF hF' ht).symm (inclusion ht a) =
      inclusion ht ((precompEquivOfLift hF hper hφ hc hcF hMF).symm a) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, precompNonposEquivOfLift_inclusion,
    ContinuousLinearEquiv.apply_symm_apply]

/-- At the order `0`, `precompNonposEquivOfLift` is the precomposition `precompEquivOfLift` on
`H⁰`. -/
@[simp]
theorem precompNonposEquivOfLift_zero :
    precompNonposEquivOfLift hF hper hφ hc hcF hMF hF' le_rfl =
      precompEquivOfLift hF hper hφ hc hcF hMF :=
  ContinuousLinearEquiv.ext <| funext fun a ↦ by
    simpa only [inclusion_refl] using precompNonposEquivOfLift_inclusion hF hper hφ hc hcF hMF hF'
      le_rfl a

/-- Precomposition on the different orders `t' ≤ t ≤ 0` is compatible with the inclusion
`H^t → H^t'`. -/
theorem inclusion_precompNonposEquivOfLift_of_le {t t' : ℝ} (ht : t ≤ 0) (htt' : t' ≤ t)
    (a : CircleSobolev t ℂ) :
    inclusion htt' (precompNonposEquivOfLift hF hper hφ hc hcF hMF hF' ht a) =
      precompNonposEquivOfLift hF hper hφ hc hcF hMF hF' (htt'.trans ht) (inclusion htt' a) := by
  -- Both sides are continuous in `a`, so it suffices to compare them on Fourier monomials, which
  -- lie in `H⁰`.
  suffices h : (inclusion htt').comp
      (precompNonposEquivOfLift hF hper hφ hc hcF hMF hF' ht :
        CircleSobolev t ℂ →L[ℂ] CircleSobolev t ℂ) =
        (precompNonposEquivOfLift hF hper hφ hc hcF hMF hF' (htt'.trans ht) :
          CircleSobolev t' ℂ →L[ℂ] CircleSobolev t' ℂ).comp (inclusion htt') from
    DFunLike.congr_fun h a
  refine continuousLinearMap_ext_single fun n x ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ← inclusion_single ht n x, precompNonposEquivOfLift_inclusion, inclusion_inclusion]

/-- For `t ≤ 0 ≤ s`, precomposition on `H^s` and on `H^t` are compatible with the inclusion
`H^s → H^t`. -/
theorem inclusion_precompSmoothEquivOfLift_of_nonpos {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 0)
    (a : CircleSobolev s ℂ) :
    inclusion (ht.trans hs) (precompSmoothEquivOfLift hF hper hφ hc hcF hMF hF' hs a) =
      precompNonposEquivOfLift hF hper hφ hc hcF hMF hF' ht (inclusion (ht.trans hs) a) := by
  rw [← inclusion_inclusion ht hs, inclusion_precompSmoothEquivOfLift,
    ← inclusion_inclusion ht hs, precompNonposEquivOfLift_inclusion]

/-- The inverse of `precompNonposEquivOfLift` is `precompNonposEquivOfLift` for the inverse map
`ψ` of the circle, presented by any lift `G` of `ψ` with smooth derivative between two positive
constants. -/
theorem precompNonposEquivOfLift_symm_eq {ψ : AddCircle T → AddCircle T} {G G' : ℝ → ℝ}
    {c' M' : ℝ} (hG : ∀ x, HasDerivAt G (G' x) x) (hperG : ∀ x, G (x + T) = G x + T)
    (hψ : ∀ x : ℝ, ψ x = G x) (hc' : 0 < c') (hcG : ∀ x, c' ≤ G' x) (hMG : ∀ x, G' x ≤ M')
    (hG' : ContDiff ℝ ∞ G') (hψφ : Function.LeftInverse ψ φ) {t : ℝ} (ht : t ≤ 0) :
    (precompNonposEquivOfLift hF hper hφ hc hcF hMF hF' ht).symm =
      precompNonposEquivOfLift hG hperG hψ hc' hcG hMG hG' ht := by
  refine ContinuousLinearEquiv.coe_injective
    (continuousLinearMap_ext_single fun n x ↦ ?_)
  simp only [ContinuousLinearEquiv.coe_coe, ← inclusion_single ht n x,
    precompNonposEquivOfLift_symm_inclusion, precompNonposEquivOfLift_inclusion,
    precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF hG hperG hψ hc' hcG hMG hψφ]

end Lift

end CircleSobolev

end TauCeti
