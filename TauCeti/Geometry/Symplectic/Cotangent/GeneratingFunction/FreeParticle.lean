/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Legendre
public import TauCeti.Geometry.Symplectic.Hamiltonian.FreeParticle
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# Generating functions of free motion

On a real Hilbert space `E`, a free particle of mass `m` moves for time `t` by the linear map
`φ_t(q, p) = (q + (t / m) p♯, p)` of the cotangent space `E × E'`
(`TauCeti.freeParticleEvolution`), where `p♯` is the Riesz representative of the covector `p`.
This file describes `φ_t` by generating functions, with the conventions of
`TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Basic`: `(q, p)` is the source and
`(Q, P)` the target of the generated relation.

* **First kind.** For `m ≠ 0` and `t ≠ 0`, the function
  `S(q, Q) = -m ‖q - Q‖² / (2t)` (`TauCeti.freeParticleGeneratingFunction`) has invertible mixed
  Hessian `(m / t) ⟪δQ, δq⟫`, its target projection is `φ_t` applied to its source projection
  (`TauCeti.cotangentGeneratingTarget_freeParticleGeneratingFunction`), and so the map it generates
  is `φ_t` near every point
  (`TauCeti.cotangentGeneratedMap_freeParticleGeneratingFunction_eventuallyEq`). At `t = 0` the
  position projection `(q, p) ↦ (q, Q)` of `φ_t` is not invertible and no first-kind function
  generates it.
* **Second kind.** For every `t`, including `t = 0`, the function
  `F₂(q, P) = P(q) + t ‖P‖² / (2m)` (`TauCeti.freeParticleSecondKindGeneratingFunction`), that is
  `P(q)` plus `t` times the kinetic energy, relates `(q, p)` to `(Q, P)` in the sense of
  `TauCeti.CotangentSecondKindRelated` exactly when `(Q, P) = φ_t(q, p)`
  (`TauCeti.cotangentSecondKindRelated_freeParticleSecondKindGeneratingFunction_iff`). At `t = 0`
  it is `P(q)`, which generates the identity. For `m ≠ 0` and `t ≠ 0` it is, near every point, the
  partial Legendre transform `TauCeti.cotangentPartialLegendre` of the first-kind function
  (`TauCeti.cotangentPartialLegendre_freeParticleGeneratingFunction_eventuallyEq`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  §48 (generating functions).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 4 (generating functions).
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter InnerProductSpace
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The generating function of the first kind -/

/-- The generating function `S(q, Q) = -m ‖q - Q‖² / (2t)` of the motion for time `t` of a free
particle of mass `m`. -/
def freeParticleGeneratingFunction (m t : ℝ) (x : E × E) : ℝ :=
  -m * ‖x.1 - x.2‖ ^ 2 / (2 * t)

omit [InnerProductSpace ℝ E] in
theorem freeParticleGeneratingFunction_apply (m t : ℝ) (x : E × E) :
    freeParticleGeneratingFunction m t x = -m * ‖x.1 - x.2‖ ^ 2 / (2 * t) :=
  (rfl)

theorem contDiff_freeParticleGeneratingFunction {n : WithTop ℕ∞} (m t : ℝ) :
    ContDiff ℝ n (freeParticleGeneratingFunction (E := E) m t) :=
  (((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)).const_smul (-m)).div_const _

/-- The derivative of the free-particle generating function, as a function of the base point. -/
private theorem fderiv_freeParticleGeneratingFunction_eq_linearMap (m t : ℝ) :
    fderiv ℝ (freeParticleGeneratingFunction (E := E) m t) =
      ⇑((-(m / t)) • (precomp ℝ (fst ℝ E E - snd ℝ E E)).comp
        ((innerSL ℝ : E →L[ℝ] StrongDual ℝ E).comp (fst ℝ E E - snd ℝ E E))) := by
  funext y
  set L := fst ℝ E E - snd ℝ E E
  have h := (hasStrictFDerivAt_norm_sq (L y)).hasFDerivAt.comp y L.hasFDerivAt
  have hS : freeParticleGeneratingFunction (E := E) m t =
      fun y ↦ -(m * (2 * t)⁻¹) * ‖L y‖ ^ 2 := by
    funext y
    simp only [freeParticleGeneratingFunction_apply, L, sub_apply, coe_fst', coe_snd']
    ring
  rw [hS]
  refine (h.const_mul (-(m * (2 * t)⁻¹))).fderiv.trans (ContinuousLinearMap.ext fun u ↦ ?_)
  simp only [_root_.smul_apply, coe_comp, Function.comp_apply, precomp_apply,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  ring

/-- The derivative of `S(q, Q) = -m ‖q - Q‖² / (2t)` applied to a variation `(δq, δQ)`. -/
theorem fderiv_freeParticleGeneratingFunction (m t : ℝ) (y u : E × E) :
    fderiv ℝ (freeParticleGeneratingFunction m t) y u =
      -(m / t) * ⟪y.1 - y.2, u.1 - u.2⟫ := by
  simp only [fderiv_freeParticleGeneratingFunction_eq_linearMap, _root_.smul_apply, coe_comp,
    Function.comp_apply, precomp_apply, _root_.sub_apply, coe_fst', coe_snd', innerSL_apply_apply,
    smul_eq_mul]

/-- The mixed Hessian of the free-particle generating function is `(m / t) ⟪δQ, δq⟫`. -/
theorem cotangentMixedHessian_freeParticleGeneratingFunction_apply_apply (m t : ℝ) (x : E × E)
    (b a : E) :
    cotangentMixedHessian (freeParticleGeneratingFunction m t) x b a = m / t * ⟪b, a⟫ := by
  rw [cotangentMixedHessian_apply_apply, fderiv_freeParticleGeneratingFunction_eq_linearMap,
    ContinuousLinearMap.fderiv]
  simp only [_root_.smul_apply, coe_comp, Function.comp_apply, precomp_apply, _root_.sub_apply,
    coe_fst', coe_snd', innerSL_apply_apply, smul_eq_mul, zero_sub, sub_zero, inner_neg_left,
    mul_neg, neg_mul, neg_neg]

/-- The negative `Q,Q` Hessian of the free-particle generating function is `(m / t) ⟪δQ, δQ'⟫`. -/
theorem cotangentLegendreHessian_freeParticleGeneratingFunction_apply_apply (m t : ℝ)
    (x : E × E) (b c : E) :
    cotangentLegendreHessian (freeParticleGeneratingFunction m t) x b c = m / t * ⟪b, c⟫ := by
  rw [cotangentLegendreHessian_apply_apply, fderiv_freeParticleGeneratingFunction_eq_linearMap,
    ContinuousLinearMap.fderiv]
  simp only [_root_.smul_apply, coe_comp, Function.comp_apply, precomp_apply, _root_.sub_apply,
    coe_fst', coe_snd', innerSL_apply_apply, smul_eq_mul, zero_sub, inner_neg_left,
    inner_neg_right, neg_neg]
  ring

variable [CompleteSpace E]

/-- The source projection of the free-particle generating function: `p = (m / t) (Q - q)♭`,
where `v♭ = ⟪v, ·⟫`. -/
@[simp]
theorem cotangentGeneratingSource_freeParticleGeneratingFunction (m t : ℝ) (q Q : E) :
    cotangentGeneratingSource (freeParticleGeneratingFunction m t) (q, Q) =
      (q, (m / t) • toDual ℝ E (Q - q)) := by
  ext a
  · simp
  · simp only [cotangentGeneratingSource_snd_apply, fderiv_freeParticleGeneratingFunction,
      _root_.smul_apply, smul_eq_mul, sub_zero, toDual_apply_apply]
    rw [← neg_sub Q q, inner_neg_left]
    ring

/-- The target projection of the free-particle generating function: `P = (m / t) (Q - q)♭`. -/
@[simp]
theorem cotangentGeneratingTarget_freeParticleGeneratingFunction_apply (m t : ℝ) (q Q : E) :
    cotangentGeneratingTarget (freeParticleGeneratingFunction m t) (q, Q) =
      (Q, (m / t) • toDual ℝ E (Q - q)) := by
  ext b
  · simp
  · simp only [cotangentGeneratingTarget_snd_apply, fderiv_freeParticleGeneratingFunction,
      _root_.smul_apply, smul_eq_mul, zero_sub, toDual_apply_apply]
    rw [← neg_sub Q q, inner_neg_left, inner_neg_right, neg_neg]
    ring

variable {m t : ℝ}

/-- For `m ≠ 0` and `t ≠ 0` the mixed Hessian of the free-particle generating function is
invertible: it is `m / t` times the Riesz isomorphism. -/
theorem isInvertible_cotangentMixedHessian_freeParticleGeneratingFunction (hm : m ≠ 0)
    (ht : t ≠ 0) (x : E × E) :
    (cotangentMixedHessian (freeParticleGeneratingFunction m t) x).IsInvertible :=
  isInvertible_of_apply_apply_eq_mul_inner (div_ne_zero hm ht)
    (cotangentMixedHessian_freeParticleGeneratingFunction_apply_apply m t x)

/-- For `m ≠ 0` and `t ≠ 0` the negative `Q,Q` Hessian of the free-particle generating function is
invertible, so its partial Legendre transform is defined near every point. -/
theorem isInvertible_cotangentLegendreHessian_freeParticleGeneratingFunction (hm : m ≠ 0)
    (ht : t ≠ 0) (x : E × E) :
    (cotangentLegendreHessian (freeParticleGeneratingFunction m t) x).IsInvertible :=
  isInvertible_of_apply_apply_eq_mul_inner (div_ne_zero hm ht)
    (cotangentLegendreHessian_freeParticleGeneratingFunction_apply_apply m t x)

/-- **The free particle.** For `m ≠ 0` and `t ≠ 0` the generating function
`-m ‖q - Q‖² / (2t)` relates `(q, p)` to the free motion `(q + (t / m) p♯, p)` of `(q, p)`. -/
theorem cotangentGeneratingTarget_freeParticleGeneratingFunction (hm : m ≠ 0) (ht : t ≠ 0)
    (x : E × E) :
    cotangentGeneratingTarget (freeParticleGeneratingFunction m t) x =
      freeParticleEvolution m t
        (cotangentGeneratingSource (freeParticleGeneratingFunction m t) x) := by
  obtain ⟨q, Q⟩ := x
  have h : (toDual ℝ E).symm ((m / t) • toDual ℝ E (Q - q)) = (m / t) • (Q - q) :=
    ext_inner_right ℝ fun a ↦ by simp [real_inner_smul_left]
  rw [cotangentGeneratingSource_freeParticleGeneratingFunction,
    cotangentGeneratingTarget_freeParticleGeneratingFunction_apply, freeParticleEvolution_apply,
    h, smul_smul, div_mul_div_cancel₀ hm, div_self ht, one_smul, add_sub_cancel]

/-- **The map generated by the free-particle generating function** is, near each point, the free
motion `(q, p) ↦ (q + (t / m) p♯, p)`. -/
theorem cotangentGeneratedMap_freeParticleGeneratingFunction_eventuallyEq (hm : m ≠ 0)
    (ht : t ≠ 0) {x₀ : E × E} (hS : ContDiffAt ℝ 2 (freeParticleGeneratingFunction m t) x₀)
    (hM : (cotangentMixedHessian (freeParticleGeneratingFunction m t) x₀).IsInvertible) :
    cotangentGeneratedMap hS hM
      =ᶠ[𝓝 (cotangentGeneratingSource (freeParticleGeneratingFunction m t) x₀)]
        freeParticleEvolution m t := by
  filter_upwards [eventually_cotangentGeneratingSource_cotangentGeneratingBranch hS hM] with y hy
  rw [cotangentGeneratedMap_def, Function.comp_apply,
    cotangentGeneratingTarget_freeParticleGeneratingFunction hm ht, hy]

/-! ### The generating function of the second kind -/

/-- The generating function of the second kind `F₂(q, P) = P(q) + t ‖P‖² / (2m)` of the motion
for time `t` of a free particle of mass `m`: the pairing `P(q)` plus `t` times the kinetic
energy. -/
def freeParticleSecondKindGeneratingFunction (m t : ℝ) (y : E × StrongDual ℝ E) : ℝ :=
  y.2 y.1 + t * freeParticleHamiltonian m y

omit [CompleteSpace E] in
theorem freeParticleSecondKindGeneratingFunction_apply (m t : ℝ) (y : E × StrongDual ℝ E) :
    freeParticleSecondKindGeneratingFunction m t y = y.2 y.1 + t * ‖y.2‖ ^ 2 / (2 * m) := by
  rw [freeParticleSecondKindGeneratingFunction, freeParticleHamiltonian_apply, mul_div_assoc]

/-- The derivative of `F₂(q, P) = P(q) + t ‖P‖² / (2m)` at `(q, P)` is
`(δq, δP) ↦ P(δq) + δP(q + (t / m) P♯)`. -/
theorem hasFDerivAt_freeParticleSecondKindGeneratingFunction (m t : ℝ) (y : E × StrongDual ℝ E) :
    HasFDerivAt (freeParticleSecondKindGeneratingFunction m t)
      (y.2.comp (fst ℝ E (StrongDual ℝ E)) +
        (ContinuousLinearMap.apply ℝ ℝ (freeParticleEvolution m t y).1).comp
          (snd ℝ E (StrongDual ℝ E))) y := by
  refine ((hasFDerivAt_pairing y).add
    ((hasFDerivAt_freeParticleHamiltonian m y).const_mul t)).congr_fderiv
      (ContinuousLinearMap.ext fun u ↦ ?_)
  simp only [_root_.add_apply, coe_comp, Function.comp_apply, coe_fst', coe_snd', apply_apply,
    _root_.smul_apply, freeParticleEvolution_apply_fst, map_add, map_smul, smul_eq_mul]
  ring

/-- **The free particle, second kind.** For every time `t`, including `t = 0`, the function
`F₂(q, P) = P(q) + t ‖P‖² / (2m)` relates `(q, p)` to `(Q, P)` exactly when `(Q, P)` is the
free motion `(q + (t / m) p♯, p)` of `(q, p)`. -/
@[simp]
theorem cotangentSecondKindRelated_freeParticleSecondKindGeneratingFunction_iff (m t : ℝ)
    (x y : E × StrongDual ℝ E) :
    CotangentSecondKindRelated (freeParticleSecondKindGeneratingFunction m t) x y ↔
      y = freeParticleEvolution m t x := by
  have hd := hasFDerivAt_freeParticleSecondKindGeneratingFunction m t (x.1, y.2)
  rw [cotangentSecondKindRelated_iff_fderiv, hd.fderiv]
  simp only [hd.differentiableAt, true_and, _root_.add_apply, coe_comp, Function.comp_apply,
    coe_fst', coe_snd', apply_apply, map_zero, add_zero, zero_add,
    freeParticleEvolution_apply_fst]
  constructor
  · rintro ⟨hp, hQ⟩
    have hp' : y.2 = x.2 := ContinuousLinearMap.ext hp
    have hQ' : x.1 + (t / m) • (toDual ℝ E).symm y.2 = y.1 :=
      (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 hQ
    rw [freeParticleEvolution_apply, ← hp', hQ']
  · rintro rfl
    simp

/-- **`F₂` is the partial Legendre transform of `S`.** For `m ≠ 0` and `t ≠ 0`, near every
mixed-coordinate point the second-kind function `P(q) + t ‖P‖² / (2m)` is the partial Legendre
transform of the first-kind function `-m ‖q - Q‖² / (2t)`. -/
theorem cotangentPartialLegendre_freeParticleGeneratingFunction_eventuallyEq (hm : m ≠ 0)
    (ht : t ≠ 0) {x₀ : E × E} (hS : ContDiffAt ℝ 2 (freeParticleGeneratingFunction m t) x₀)
    (hM : (cotangentLegendreHessian (freeParticleGeneratingFunction m t) x₀).IsInvertible) :
    cotangentPartialLegendre hS hM
      =ᶠ[𝓝 (cotangentLegendreProjection (freeParticleGeneratingFunction m t) x₀)]
        freeParticleSecondKindGeneratingFunction m t := by
  let g : E × StrongDual ℝ E → E × E := fun y ↦ (y.1, (freeParticleEvolution m t y).1)
  have hg : g =ᶠ[𝓝 (cotangentLegendreProjection (freeParticleGeneratingFunction m t) x₀)]
      (cotangentLegendreChart hS hM).symm := by
    refine eventuallyEq_cotangentLegendreChart_symm hS hM (Eventually.of_forall fun x ↦ ?_)
    obtain ⟨q, Q⟩ := x
    ext1
    · simp [g]
    · simp [g, smul_smul, div_mul_div_cancel₀ hm, div_self ht]
  filter_upwards [hg] with y hy
  rw [cotangentPartialLegendre_def, ← hy, freeParticleSecondKindGeneratingFunction_apply,
    freeParticleGeneratingFunction_apply]
  simp only [g, freeParticleEvolution_apply_fst, sub_add_cancel_left, norm_neg, norm_smul,
    LinearIsometryEquiv.norm_map, map_add, map_smul, smul_eq_mul, Real.norm_eq_abs, mul_pow,
    sq_abs]
  rw [apply_toDual_symm_self, RCLike.ofReal_real_eq_id, id]
  field_simp
  ring

/-- At time zero, `F₂(q, P) = P(q)` generates the identity. -/
theorem cotangentSecondKindRelated_freeParticleSecondKindGeneratingFunction_zero_iff (m : ℝ)
    (x y : E × StrongDual ℝ E) :
    CotangentSecondKindRelated (freeParticleSecondKindGeneratingFunction m 0) x y ↔ y = x := by
  rw [cotangentSecondKindRelated_freeParticleSecondKindGeneratingFunction_iff,
    freeParticleEvolution_zero, ContinuousLinearMap.id_apply]

end TauCeti
