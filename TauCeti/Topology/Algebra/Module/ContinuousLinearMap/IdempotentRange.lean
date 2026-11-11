/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Abel

/-!
# Ranges of intertwined projections

For idempotent continuous linear maps `p` and `q` on a topological module, the operator
`U = q * p + (1 - q) * (1 - p)` satisfies `q * U = U * p`. When `U` is invertible, it therefore
carries the range of `p` isomorphically onto the range of `q`
(`ContinuousLinearMap.IsIdempotentElem.rangeEquiv`), and the kernel of `p` onto the kernel of `q`
(`ContinuousLinearMap.IsIdempotentElem.map_ker_eq_ker`). This is the intertwining operator of a
pair of projections; it is the local chart of the image bundle of a continuous family of
projections, and it shows that nearby projections have isomorphic ranges.

The operator `U` is injective exactly when the range of each projection meets the kernel of the
other only in `0`
(`ContinuousLinearMap.IsIdempotentElem.injective_mul_add_one_sub_mul_one_sub_iff`).
In finite dimension this characterizes the invertibility of `U`
(`ContinuousLinearMap.IsIdempotentElem.isUnit_mul_add_one_sub_mul_one_sub_iff`): two splittings
`range p ⊕ ker p` and `range q ⊕ ker q` are then carried onto each other by a single invertible
operator, with no smallness condition on `p - q`.

For a retract `r ∘ i = id` of `M` through `N`, the extension `i ∘ e ∘ r` of an endomorphism `e`
of `M` is idempotent when `e` is, and `i` identifies the range of `e` with the range of
`i ∘ e ∘ r` (`ContinuousLinearMap.rangeEquivOfRetract`).

A pseudo-inverse `g` of `f`, with `f ∘ g ∘ f = f`, gives the projection `g ∘ f`
(`ContinuousLinearMap.isIdempotentElem_comp_of_comp_comp_eq_self`).

## Main definitions

* `ContinuousLinearMap.IsIdempotentElem.rangeEquiv`: the isomorphism of the ranges of `p` and
  `q` induced by `q * p + (1 - q) * (1 - p)`, when that operator is invertible.
* `ContinuousLinearMap.rangeEquivOfRetract`: the identification of the range of `e` with the
  range of its extension `i ∘ e ∘ r` along a retract.

## Main results

* `ContinuousLinearMap.IsIdempotentElem.apply_coe_range`: an idempotent continuous linear map
  fixes every vector of its range.
* `ContinuousLinearMap.IsIdempotentElem.mul_self_add_one_sub_mul_one_sub`: the operator
  `p * p + (1 - p) * (1 - p)` intertwining an idempotent `p` with itself is the identity.
* `ContinuousLinearMap.IsIdempotentElem.map_range_eq_range` and
  `ContinuousLinearMap.IsIdempotentElem.map_ker_eq_ker`: an invertible intertwiner carries the range
  and the kernel of `p` onto those of `q`.
* `ContinuousLinearMap.IsIdempotentElem.injective_mul_add_one_sub_mul_one_sub_iff` and
  `ContinuousLinearMap.IsIdempotentElem.isUnit_mul_add_one_sub_mul_one_sub_iff`: the intertwiner is
  injective, and in finite dimension invertible, exactly when `range p ⊓ ker q = ⊥` and
  `ker p ⊓ range q = ⊥`.
* `ContinuousLinearMap.isIdempotentElem_comp_comp_of_retract`: the extension of an idempotent
  along a retract is idempotent.
* `ContinuousLinearMap.isIdempotentElem_comp_of_comp_comp_eq_self`: if `g` is a pseudo-inverse
  of `f`, then `g ∘ f` is a continuous projection.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6, for the
  intertwining operator of a pair of projections.
-/

public section

open scoped Ring

namespace ContinuousLinearMap.IsIdempotentElem

variable {R M : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  {p q : M →L[R] M}

/-- An idempotent continuous linear map fixes every vector of its range. -/
@[simp]
theorem apply_coe_range (hp : IsIdempotentElem p) (w : p.range) : p w = w :=
  (LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp)).mp w.2

variable [IsTopologicalAddGroup M]

/-- The operator `p * p + (1 - p) * (1 - p)`, which intertwines an idempotent `p` with itself, is
the identity. -/
theorem mul_self_add_one_sub_mul_one_sub (hp : IsIdempotentElem p) :
    p * p + (1 - p) * (1 - p) = 1 := by
  rw [hp.eq, hp.one_sub.eq, add_sub_cancel]

/-- The operator `p * p + (1 - p) * (1 - p)` is invertible for an idempotent `p`. -/
theorem isUnit_mul_self_add_one_sub_mul_one_sub (hp : IsIdempotentElem p) :
    IsUnit (p * p + (1 - p) * (1 - p)) := by
  rw [mul_self_add_one_sub_mul_one_sub hp]
  exact isUnit_one

/-- The operator `q * p + (1 - q) * (1 - p)`, which intertwines `p` with `q`. -/
private def intertwiner (p q : M →L[R] M) : M →L[R] M :=
  q * p + (1 - q) * (1 - p)

private theorem mul_intertwiner (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    q * intertwiner p q = intertwiner p q * p := by
  have h := hq.eq
  have h₀ := hp.eq
  simp only [intertwiner, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, ← mul_assoc, h]
  simp only [mul_assoc, h₀]
  abel

/-- Where the intertwiner is invertible, its inverse intertwines `q` with `p`. -/
private theorem inverse_intertwiner_mul (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hU : IsUnit (intertwiner p q)) :
    (intertwiner p q)⁻¹ʳ * q = p * (intertwiner p q)⁻¹ʳ := by
  have h := congr((intertwiner p q)⁻¹ʳ * $(mul_intertwiner hp hq) * (intertwiner p q)⁻¹ʳ)
  simpa only [mul_assoc, Ring.mul_inverse_cancel _ hU, Ring.inverse_mul_cancel_left _ _ hU,
    mul_one] using h

private theorem apply_intertwiner (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (v : M) :
    q (intertwiner p q v) = intertwiner p q (p v) :=
  congr($(mul_intertwiner hp hq) v)

private theorem inverse_intertwiner_apply (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hU : IsUnit (intertwiner p q)) (v : M) :
    (intertwiner p q)⁻¹ʳ (q v) = p ((intertwiner p q)⁻¹ʳ v) :=
  congr($(inverse_intertwiner_mul hp hq hU) v)

private theorem intertwiner_mem_range (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (w : p.range) : intertwiner p q w ∈ q.range :=
  ⟨intertwiner p q w,
    (apply_intertwiner hp hq w).trans congr(intertwiner p q $(apply_coe_range hp w))⟩

private theorem inverse_intertwiner_mem_range (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (hU : IsUnit (intertwiner p q)) (w : q.range) :
    (intertwiner p q)⁻¹ʳ w ∈ p.range :=
  ⟨(intertwiner p q)⁻¹ʳ w,
    (inverse_intertwiner_apply hp hq hU w).symm.trans
      congr((intertwiner p q)⁻¹ʳ $(apply_coe_range hq w))⟩

/-- **Intertwined projections have isomorphic ranges.** For idempotents `p` and `q` such that
`U = q * p + (1 - q) * (1 - p)` is invertible, `U` restricts to an isomorphism from the range
of `p` onto the range of `q`, with inverse the restriction of `U⁻¹`. -/
noncomputable def rangeEquiv (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hU : IsUnit (q * p + (1 - q) * (1 - p))) : p.range ≃L[R] q.range :=
  .equivOfInverse ((intertwiner p q ∘L p.range.subtypeL).codRestrict q.range
      (intertwiner_mem_range hp hq))
    (((intertwiner p q)⁻¹ʳ ∘L q.range.subtypeL).codRestrict p.range
      (inverse_intertwiner_mem_range hp hq hU))
    (fun w ↦ Subtype.ext (congr($(Ring.inverse_mul_cancel _ hU) (w : M))))
    (fun w ↦ Subtype.ext (congr($(Ring.mul_inverse_cancel _ hU) (w : M))))

section

variable (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
  (hU : IsUnit (q * p + (1 - q) * (1 - p)))
include hp hq hU

/-- The isomorphism of ranges applies `q * p + (1 - q) * (1 - p)`. -/
@[simp]
theorem coe_rangeEquiv_apply (w : p.range) :
    (rangeEquiv hp hq hU w : M) = (q * p + (1 - q) * (1 - p)) w :=
  (rfl)

/-- The inverse isomorphism of ranges applies the inverse of `q * p + (1 - q) * (1 - p)`. -/
@[simp]
theorem coe_rangeEquiv_symm_apply (w : q.range) :
    ((rangeEquiv hp hq hU).symm w : M) = (q * p + (1 - q) * (1 - p))⁻¹ʳ w :=
  (rfl)

/-- **An invertible intertwiner carries range onto range.** For idempotents `p` and `q` such that
`U = q * p + (1 - q) * (1 - p)` is invertible, `U` maps the range of `p` onto the range of `q`. -/
theorem map_range_eq_range :
    p.range.map ((q * p + (1 - q) * (1 - p) : M →L[R] M) : M →ₗ[R] M) = q.range := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun w hw ↦ ?_) fun w hw ↦ ?_
  · exact (rangeEquiv hp hq hU ⟨w, hw⟩).2
  · refine ⟨_, ((rangeEquiv hp hq hU).symm ⟨w, hw⟩).2, ?_⟩
    rw [ContinuousLinearMap.coe_coe, ← coe_rangeEquiv_apply hp hq hU,
      ContinuousLinearEquiv.apply_symm_apply]

/-- **An invertible intertwiner carries kernel onto kernel.** For idempotents `p` and `q` such that
`U = q * p + (1 - q) * (1 - p)` is invertible, `U` maps the kernel of `p` onto the kernel of `q`.
-/
theorem map_ker_eq_ker :
    p.ker.map ((q * p + (1 - q) * (1 - p) : M →L[R] M) : M →ₗ[R] M) = q.ker := by
  -- The intertwiner of the complementary projections `1 - p` and `1 - q` is the same operator.
  have hU' : (1 - q) * (1 - p) + (1 - (1 - q)) * (1 - (1 - p)) = q * p + (1 - q) * (1 - p) := by
    rw [sub_sub_cancel, sub_sub_cancel, add_comm]
  have h := map_range_eq_range hp.one_sub hq.one_sub (hU' ▸ hU)
  rwa [hU', ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_one,
    ← LinearMap.IsIdempotentElem.ker_eq_range_one_sub (toLinearMap hp),
    ← LinearMap.IsIdempotentElem.ker_eq_range_one_sub (toLinearMap hq)] at h

end

/-- **Injectivity of the intertwiner.** For idempotents `p` and `q`, the operator
`q * p + (1 - q) * (1 - p)` is injective exactly when the range of `p` meets the kernel of `q`
only in `0`, and the kernel of `p` meets the range of `q` only in `0`. -/
theorem injective_mul_add_one_sub_mul_one_sub_iff (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) :
    Function.Injective ⇑(q * p + (1 - q) * (1 - p) : M →L[R] M) ↔
      Disjoint p.range q.ker ∧ Disjoint p.ker q.range := by
  have hp' (v : M) := LinearMap.IsIdempotentElem.mem_range_iff (toLinearMap hp) (x := v)
  have hq' (v : M) := LinearMap.IsIdempotentElem.mem_range_iff (toLinearMap hq) (x := v)
  have hpp (v : M) : p (p v) = p v := congr($hp.eq v)
  have hqq (v : M) : q (q v) = q v := congr($hq.eq v)
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ker_eq_bot, Submodule.disjoint_def,
    Submodule.disjoint_def]
  refine ⟨fun h ↦ ⟨fun v hvp hvq ↦ ?_, fun v hvp hvq ↦ ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · -- On the range of `p` the intertwiner is `q`.
    refine (Submodule.mem_bot R).1 (h ▸ LinearMap.mem_ker.2 ?_)
    have hv : p v = v := (hp' v).1 hvp
    simp [hv, LinearMap.mem_ker.1 hvq]
  · -- On the kernel of `p` the intertwiner is `1 - q`.
    refine (Submodule.mem_bot R).1 (h ▸ LinearMap.mem_ker.2 ?_)
    have hv : q v = v := (hq' v).1 hvq
    simp [hv, LinearMap.mem_ker.1 hvp]
  · refine (Submodule.eq_bot_iff _).2 fun v hv ↦ ?_
    have hv : q (p v) + (v - p v - (q v - q (p v))) = 0 := by simpa using LinearMap.mem_ker.1 hv
    -- Applying `q` to the equation kills its second summand, so `q (p v) = 0` and then
    -- `v - p v = q v`; the two disjointness conditions force `p v = 0` and `v - p v = 0`.
    have h0 : q (p v) = 0 := by simpa [hqq] using congr(q $hv)
    rw [h0, sub_zero, zero_add, sub_eq_zero] at hv
    have h1 : v - p v = 0 := by
      refine h₂ _ (LinearMap.mem_ker.2 (by simp [hpp])) ((hq' (v - p v)).2 ?_)
      rw [map_sub, ContinuousLinearMap.coe_coe, h0, sub_zero, hv]
    have h2 : p v = 0 := h₁ _ (LinearMap.mem_range_self _ v) h0
    rw [← sub_add_cancel v (p v), h1, h2, add_zero]

/-- **Invertibility of the intertwiner in finite dimension.** For idempotents `p` and `q` on a
finite-dimensional Hausdorff topological vector space over a complete field, the operator
`q * p + (1 - q) * (1 - p)` is invertible exactly when the range of `p` meets the kernel of `q`
only in `0`, and the kernel of `p` meets the range of `q` only in `0`. -/
theorem isUnit_mul_add_one_sub_mul_one_sub_iff {𝕜 M : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousSMul 𝕜 M] [T2Space M] [FiniteDimensional 𝕜 M] {p q : M →L[𝕜] M}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    IsUnit (q * p + (1 - q) * (1 - p)) ↔ Disjoint p.range q.ker ∧ Disjoint p.ker q.range := by
  rw [← injective_mul_add_one_sub_mul_one_sub_iff hp hq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (ContinuousLinearEquiv.unitsEquiv 𝕜 M h.unit).injective
  · -- An injective endomorphism of a finite-dimensional space is bijective.
    let e := (LinearEquiv.ofInjectiveEndo _ h).toContinuousLinearEquiv
    have he (v : M) : e v = (q * p + (1 - q) * (1 - p)) v :=
      congr_fun (LinearEquiv.coe_ofInjectiveEndo _ h) v
    refine ⟨⟨_, e.symm, ContinuousLinearMap.ext fun v ↦ ?_, ContinuousLinearMap.ext fun v ↦ ?_⟩,
      rfl⟩
    · simpa [he] using e.apply_symm_apply v
    · simpa [he] using e.symm_apply_apply v

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
