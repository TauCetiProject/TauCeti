/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.SpectralMapping

/-!
# The partial inverse of an injective continuous operator

Let `S : X →L[𝕜] X` be an injective continuous linear operator. Its inverse
`A = S⁻¹`, read as a partial linear map with domain the range of `S`
(Mathlib's `LinearPMap.inverse` applied to `S` on the full domain), is in general unbounded:
this is how unbounded differential operators arise from their bounded solution operators. The
solution operator of an elliptic boundary value problem is such an `S`, and `A` is the
realization of the differential operator with the boundary condition.

The resolvent theory of `A` is read off from `S`. Since `(0 • I - A)⁻¹ = -S`, the scalar `0`
is a resolvent point of `A` with resolvent `-S`
(`ContinuousLinearMap.isResolventAt_inverse_toPMap_top_zero`). Resolvent spectral mapping then
identifies the rest of the spectrum: over a field, `κ` lies in the spectrum of `A` exactly when
`κ ≠ 0` and `κ⁻¹` lies in the spectrum of `S`
(`ContinuousLinearMap.mem_spectrum_inverse_toPMap_top_iff`). If `S` is compact, then `A` has
compact resolvent.

## Main results

* `ContinuousLinearMap.domain_inverse_toPMap_top`: the domain of `A` is the range of `S`, and
  `ContinuousLinearMap.inverse_toPMap_top_apply` evaluates `A (S x) = x`.
* `ContinuousLinearMap.mem_graph_inverse_toPMap_top_iff`: `(y, x)` lies on the graph of `A`
  exactly when `S x = y`.
* `ContinuousLinearMap.isResolventAt_inverse_toPMap_top_zero`: `-S` inverts `0 • I - A`.
* `ContinuousLinearMap.mem_spectrum_inverse_toPMap_top_iff`: the spectrum of `A` is the set of
  reciprocals of the nonzero spectral values of `S`.
* `ContinuousLinearMap.hasCompactResolvent_inverse_toPMap_top`: `A` has compact resolvent when
  `S` is compact.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Section III.6.
* Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section IV.1.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open LinearPMap

section Ring

variable {𝕜 X : Type*} [Ring 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  {S : X →L[𝕜] X}

/-- An injective continuous operator, read as a partial linear map on the full domain, has
trivial kernel; this is the hypothesis under which Mathlib's `LinearPMap.inverse` is a genuine
inverse. -/
theorem ker_toPMap_top_eq_bot (hS : Function.Injective S) :
    ((S : X →ₗ[𝕜] X).toPMap ⊤).ker = ⊥ :=
  LinearPMap.ker_eq_bot.2 fun _ _ hxy ↦ Subtype.ext (hS hxy)

/-- The domain of the partial inverse of `S` is the range of `S`. -/
theorem domain_inverse_toPMap_top :
    ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse.domain = LinearMap.range (S : X →ₗ[𝕜] X) := by
  rw [inverse_domain]
  ext y
  simp only [LinearMap.mem_range, LinearMap.toPMap, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_subtype, Subtype.exists, Submodule.mem_top, exists_true_left]

/-- `S x` lies in the domain of the partial inverse of `S`. -/
theorem apply_mem_domain_inverse_toPMap_top (x : X) :
    S x ∈ ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse.domain := by
  rw [domain_inverse_toPMap_top]
  exact ⟨x, rfl⟩

/-- The partial inverse of an injective `S` undoes `S`: `S⁻¹ (S x) = x`. -/
@[simp]
theorem inverse_toPMap_top_apply (hS : Function.Injective S) (x : X)
    (hx : S x ∈ ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse.domain) :
    ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse ⟨S x, hx⟩ = x :=
  inverse_apply_eq (y := ⟨S x, hx⟩) (x := ⟨x, Submodule.mem_top⟩) (ker_toPMap_top_eq_bot hS)
    rfl

/-- The graph of the partial inverse of an injective `S` is the reversed graph of `S`. -/
theorem mem_graph_inverse_toPMap_top_iff (hS : Function.Injective S) {p : X × X} :
    p ∈ ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse.graph ↔ S p.2 = p.1 := by
  rw [inverse_graph (ker_toPMap_top_eq_bot hS)]
  simp only [Submodule.mem_map, mem_graph_iff, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨y, rfl, rfl⟩, rfl⟩
    rfl
  · intro h
    exact ⟨p.2, p.1, ⟨⟨p.2, Submodule.mem_top⟩, rfl, h⟩, by simp⟩

/-- `S⁻¹ y = x` exactly when `S x = y`. -/
theorem inverse_toPMap_top_apply_eq_iff (hS : Function.Injective S)
    (y : ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse.domain) (x : X) :
    ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse y = x ↔ S x = y := by
  rw [← mem_graph_inverse_toPMap_top_iff hS (p := ((y : X), x)), mem_graph_iff]
  constructor
  · rintro rfl
    exact ⟨y, rfl, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact congrArg _ (Subtype.ext hz.symm)

/-- **`0` is a resolvent point of the partial inverse**, with resolvent `-S`: the inverse of
`0 • I - S⁻¹ = -S⁻¹` is `-S`. -/
theorem isResolventAt_inverse_toPMap_top_zero [IsTopologicalAddGroup X]
    (hS : Function.Injective S) :
    IsResolventAt ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse 0 (-S) where
  mem_domain y := by
    rw [_root_.neg_apply, ← _root_.map_neg]
    exact apply_mem_domain_inverse_toPMap_top (-y)
  smul_sub_apply y := by
    rw [zero_smul, zero_sub, neg_eq_iff_eq_neg, inverse_toPMap_top_apply_eq_iff hS]
    simp
  apply_smul_sub x := by
    obtain ⟨x, hx⟩ := x
    have hx' := hx
    rw [domain_inverse_toPMap_top] at hx'
    obtain ⟨z, rfl⟩ := hx'
    have h := inverse_toPMap_top_apply hS z hx
    simp only [ContinuousLinearMap.coe_coe] at h ⊢
    rw [h, zero_smul, zero_sub, _root_.map_neg, _root_.neg_apply, neg_neg]

/-- `0` lies in the resolvent set of the partial inverse of an injective `S`. -/
theorem zero_mem_resolventSet_inverse_toPMap_top [IsTopologicalAddGroup X]
    (hS : Function.Injective S) :
    (0 : 𝕜) ∈ ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse.resolventSet :=
  (isResolventAt_inverse_toPMap_top_zero hS).mem_resolventSet

/-- The resolvent at `0` of the partial inverse of `S` is `-S`. -/
theorem resolvent_inverse_toPMap_top_zero [IsTopologicalAddGroup X]
    (hS : Function.Injective S) :
    ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse.resolvent 0 = -S :=
  resolvent_eq_of_isResolventAt (isResolventAt_inverse_toPMap_top_zero hS)

/-- The partial inverse of an injective compact operator has compact resolvent. -/
theorem hasCompactResolvent_inverse_toPMap_top [IsTopologicalAddGroup X] (hS : Function.Injective S)
    (hc : IsCompactOperator S) : ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse.HasCompactResolvent := by
  refine HasCompactResolvent.of_isCompactOperator_resolvent
    (zero_mem_resolventSet_inverse_toPMap_top hS) ?_
  rw [resolvent_inverse_toPMap_top_zero hS]
  exact hc.neg

end Ring

section Field

variable {𝕜 X : Type*} [Field 𝕜] [AddCommGroup X] [TopologicalSpace X] [Module 𝕜 X]
  [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X] {S : X →L[𝕜] X}

/-- **The spectrum of the partial inverse.** For an injective continuous operator `S`, a scalar
`κ` lies in the spectrum of `S⁻¹` exactly when `κ ≠ 0` and `κ⁻¹` lies in the spectrum of `S`. -/
theorem mem_spectrum_inverse_toPMap_top_iff (hS : Function.Injective S) {κ : 𝕜} :
    κ ∈ ((S : X →ₗ[𝕜] X).toPMap ⊤).inverse.spectrum ↔ κ ≠ 0 ∧ κ⁻¹ ∈ _root_.spectrum 𝕜 S := by
  have h0 := zero_mem_resolventSet_inverse_toPMap_top hS
  rcases eq_or_ne κ 0 with rfl | hκ
  · simpa using h0
  have h := TauCeti.LinearPMap.notMem_spectrum_resolvent_iff h0 (neg_ne_zero.2 (inv_ne_zero hκ))
  rw [resolvent_inverse_toPMap_top_zero hS, ← spectrum.neg_eq, Set.neg_mem_neg, inv_neg, inv_inv,
    zero_sub, neg_neg] at h
  rw [mem_spectrum_iff, ← h, not_not]
  exact ⟨fun h' ↦ ⟨hκ, h'⟩, fun h' ↦ h'.2⟩

end Field

end ContinuousLinearMap
