/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.Algebra.Star.Projection.Intertwiner

/-!
# Ranges of intertwined projections

For idempotent continuous linear maps `p` and `q` on a topological module, Kato's intertwiner
`U = TauCeti.projectionIntertwiner p q = q * p + (1 - q) * (1 - p)` satisfies `q * U = U * p`.
When `U` is invertible, it therefore carries the range of `p` isomorphically onto the range of `q`
(`ContinuousLinearMap.IsIdempotentElem.rangeEquiv`). This is the intertwining operator of a pair
of projections; it is the local chart of the image bundle of a continuous family of projections,
and it shows that nearby projections have isomorphic ranges.

For a retract `r ∘ i = id` of `M` through `N`, the extension `i ∘ e ∘ r` of an endomorphism `e`
of `M` is idempotent when `e` is, and `i` identifies the range of `e` with the range of
`i ∘ e ∘ r` (`ContinuousLinearMap.rangeEquivOfRetract`).

A pseudo-inverse `g` of `f`, with `f ∘ g ∘ f = f`, gives the projection `g ∘ f`
(`ContinuousLinearMap.isIdempotentElem_comp_of_comp_comp_eq_self`).

## Main definitions

* `ContinuousLinearMap.IsIdempotentElem.rangeEquiv`: the isomorphism of the ranges of `p` and
  `q` induced by `TauCeti.projectionIntertwiner p q`, when that operator is invertible.
* `ContinuousLinearMap.rangeEquivOfRetract`: the identification of the range of `e` with the
  range of its extension `i ∘ e ∘ r` along a retract.

## Main results

* `ContinuousLinearMap.IsIdempotentElem.apply_coe_range`: an idempotent continuous linear map
  fixes every vector of its range.
* `ContinuousLinearMap.IsIdempotentElem.completeSpace_range`: the range of an idempotent
  continuous linear map on a complete space is complete.
* `ContinuousLinearMap.isIdempotentElem_comp_comp_of_retract`: the extension of an idempotent
  along a retract is idempotent.
* `ContinuousLinearMap.isIdempotentElem_comp_of_comp_comp_eq_self`: if `g` is a pseudo-inverse
  of `f`, then `g ∘ f` is a continuous projection.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6, for the
  intertwining operator of a pair of projections.
-/

public section

open TauCeti
open scoped Ring

namespace ContinuousLinearMap.IsIdempotentElem

variable {R M : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  {p q : M →L[R] M}

/-- An idempotent continuous linear map fixes every vector of its range. -/
@[simp]
theorem apply_coe_range (hp : IsIdempotentElem p) (w : p.range) : p w = w :=
  (LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp)).mp w.property

variable [IsTopologicalAddGroup M]

/-- Where the intertwiner is invertible, its inverse intertwines `q` with `p`. -/
private theorem inverse_intertwiner_mul (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hU : IsUnit (projectionIntertwiner p q)) :
    (projectionIntertwiner p q)⁻¹ʳ * q = p * (projectionIntertwiner p q)⁻¹ʳ := by
  have h := congr((projectionIntertwiner p q)⁻¹ʳ *
    $(hp.mul_projectionIntertwiner_eq_projectionIntertwiner_mul hq) *
    (projectionIntertwiner p q)⁻¹ʳ)
  simpa only [mul_assoc, Ring.mul_inverse_cancel _ hU, Ring.inverse_mul_cancel_left _ _ hU,
    mul_one] using h

private theorem apply_intertwiner (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (v : M) :
    q (projectionIntertwiner p q v) = projectionIntertwiner p q (p v) :=
  congr($(hp.mul_projectionIntertwiner_eq_projectionIntertwiner_mul hq) v)

private theorem inverse_intertwiner_apply (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hU : IsUnit (projectionIntertwiner p q)) (v : M) :
    (projectionIntertwiner p q)⁻¹ʳ (q v) = p ((projectionIntertwiner p q)⁻¹ʳ v) :=
  congr($(inverse_intertwiner_mul hp hq hU) v)

private theorem intertwiner_mem_range (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (w : p.range) : projectionIntertwiner p q w ∈ q.range :=
  ⟨projectionIntertwiner p q w,
    (apply_intertwiner hp hq w).trans congr(projectionIntertwiner p q $(apply_coe_range hp w))⟩

private theorem inverse_intertwiner_mem_range (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (hU : IsUnit (projectionIntertwiner p q)) (w : q.range) :
    (projectionIntertwiner p q)⁻¹ʳ w ∈ p.range :=
  ⟨(projectionIntertwiner p q)⁻¹ʳ w,
    (inverse_intertwiner_apply hp hq hU w).symm.trans
      congr((projectionIntertwiner p q)⁻¹ʳ $(apply_coe_range hq w))⟩

/-- **Intertwined projections have isomorphic ranges.** For idempotents `p` and `q` such that
`U = TauCeti.projectionIntertwiner p q` is invertible, `U` restricts to an isomorphism from the
range of `p` onto the range of `q`, with inverse the restriction of `U⁻¹`. -/
noncomputable def rangeEquiv (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hU : IsUnit (projectionIntertwiner p q)) : p.range ≃L[R] q.range :=
  .ofContinuousLinearMap ((projectionIntertwiner p q ∘L p.range.subtypeL).codRestrict q.range
      (intertwiner_mem_range hp hq))
    (((projectionIntertwiner p q)⁻¹ʳ ∘L q.range.subtypeL).codRestrict p.range
      (inverse_intertwiner_mem_range hp hq hU))
    (ContinuousLinearMap.ext fun w ↦ Subtype.ext (congr($(Ring.mul_inverse_cancel _ hU) (w : M))))
    (ContinuousLinearMap.ext fun w ↦ Subtype.ext (congr($(Ring.inverse_mul_cancel _ hU) (w : M))))

variable (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
  (hU : IsUnit (projectionIntertwiner p q))

/-- The isomorphism of ranges applies `TauCeti.projectionIntertwiner p q`. -/
@[simp]
theorem coe_rangeEquiv_apply (w : p.range) :
    (rangeEquiv hp hq hU w : M) = projectionIntertwiner p q w :=
  (rfl)

/-- The inverse isomorphism of ranges applies the inverse of `TauCeti.projectionIntertwiner p q`. -/
@[simp]
theorem coe_rangeEquiv_symm_apply (w : q.range) :
    ((rangeEquiv hp hq hU).symm w : M) = (projectionIntertwiner p q)⁻¹ʳ w :=
  (rfl)

/-- The range of an idempotent continuous linear map on a complete space is complete. -/
theorem completeSpace_range {R M : Type*} [Ring R] [UniformSpace M] [T1Space M] [CompleteSpace M]
    [AddCommGroup M] [IsTopologicalAddGroup M] [Module R M] {p : M →L[R] M}
    (hp : IsIdempotentElem p) : CompleteSpace p.range :=
  (isClosed_range hp).completeSpace_coe

end ContinuousLinearMap.IsIdempotentElem

namespace ContinuousLinearMap

/-- If `g` is a pseudo-inverse of `f`, that is `f ∘ g ∘ f = f`, then `g ∘ f` is a projection. -/
theorem isIdempotentElem_comp_of_comp_comp_eq_self {R M N : Type*} [Semiring R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] [TopologicalSpace N] [AddCommMonoid N]
    [Module R N] {f : M →L[R] N} {g : N →L[R] M} (hfg : f ∘L g ∘L f = f) :
    IsIdempotentElem (g ∘L f) := by
  ext v
  simpa using congrArg g congr($hfg v)

section Retract

variable {R M N : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [TopologicalSpace N] [AddCommMonoid N] [Module R N] {i : M →L[R] N} {r : N →L[R] M}

/-- For a retract `r ∘ i = id` of `M` through `N`, the extension `i ∘ e ∘ r` of an idempotent `e`
of `M` is an idempotent of `N`. -/
theorem isIdempotentElem_comp_comp_of_retract {e : M →L[R] M} (he : IsIdempotentElem e)
    (hri : r.comp i = .id R M) : IsIdempotentElem (i.comp (e.comp r)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hee (x : M) : e (e x) = e x := congr($he.eq x)
  ext x : 1
  simp [hri', hee]

/-- For a retract `r ∘ i = id` of `M` through `N`, the inclusion `i` identifies the range of an
endomorphism `e` of `M` with the range of its extension `i ∘ e ∘ r`. -/
noncomputable def rangeEquivOfRetract (e : M →L[R] M) (hri : r.comp i = .id R M) :
    LinearMap.range (e : M →ₗ[R] M) ≃ₗ[R]
      LinearMap.range ((i : M →ₗ[R] N) ∘ₗ (e : M →ₗ[R] M) ∘ₗ (r : N →ₗ[R] M)) :=
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  (Submodule.equivMapOfInjective (i : M →ₗ[R] N) (Function.LeftInverse.injective hri') _).trans
    (LinearEquiv.ofEq _ _ (by
      rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top]
      exact LinearMap.range_eq_top.2 (Function.LeftInverse.surjective hri')))

/-- The identification of ranges along a retract applies the inclusion `i`. -/
@[simp]
theorem coe_rangeEquivOfRetract_apply (e : M →L[R] M) (hri : r.comp i = .id R M)
    (x : LinearMap.range (e : M →ₗ[R] M)) : (rangeEquivOfRetract e hri x : N) = i x :=
  (rfl)

/-- The inverse identification of ranges along a retract applies the retraction `r`. -/
@[simp]
theorem coe_rangeEquivOfRetract_symm_apply (e : M →L[R] M) (hri : r.comp i = .id R M)
    (y : LinearMap.range ((i : M →ₗ[R] N) ∘ₗ (e : M →ₗ[R] M) ∘ₗ (r : N →ₗ[R] M))) :
    ((rangeEquivOfRetract e hri).symm y : M) = r y := by
  obtain ⟨x, rfl⟩ := (rangeEquivOfRetract e hri).surjective y
  rw [LinearEquiv.symm_apply_apply, coe_rangeEquivOfRetract_apply]
  exact (DFunLike.congr_fun hri (x : M)).symm

end Retract

end ContinuousLinearMap
