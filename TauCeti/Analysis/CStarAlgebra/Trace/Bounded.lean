/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Trace.Domain

/-!
# Bounded traces are positive tracial functionals

A trace `τ` on a C⋆-algebra `B` (`TauCeti.IsTrace`) that is finite on `B₊` is the restriction to
`B₊` of a positive tracial functional, and this functional is unique. Since `τ` is finite on
`B₊`, its domain `𝔪_τ` is all of `B` (`TauCeti.domain_eq_top_of_lt_top`), so the linear
extension `TauCeti.IsTrace.linearMap` of `τ` is a linear functional on `B`. It is positive
because it equals `τ` on `B₊`, and tracial by `TauCeti.IsTrace.linearMap_mul_comm`. Uniqueness
holds because `B₊` spans `B`.

Conversely, the trace `TauCeti.PositiveTracialFunctional.toTrace` of a positive tracial
functional is finite everywhere, so the bounded traces are exactly the traces of positive tracial
functionals (`TauCeti.IsTrace.forall_lt_top_iff_exists_positiveFunctional`).

## Main definitions

* `TauCeti.IsTrace.toPositiveTracialFunctional`: the positive tracial functional of a trace that
  is finite on `B₊`.

## Main results

* `TauCeti.IsTrace.toTrace_toPositiveTracialFunctional_of_nonneg`: it restricts to `τ` on `B₊`.
* `TauCeti.IsTrace.exists_positiveFunctional`: a trace finite on `B₊` is the restriction to `B₊`
  of a positive tracial functional.
* `TauCeti.IsTrace.forall_lt_top_iff_exists_positiveFunctional`: a trace is finite on `B₊` if and
  only if it is the restriction to `B₊` of a positive tracial functional.
* `TauCeti.PositiveTracialFunctional.ext_of_toTrace`: a positive tracial functional is determined
  by its trace on `B₊`, and so
  `TauCeti.IsTrace.eq_toPositiveTracialFunctional_of_toTrace`: the functional above is unique.
* `TauCeti.PositiveTracialFunctional.toPositiveTracialFunctional_toTrace`: the construction
  recovers every positive tracial functional from its trace.

## References

* Jacques Dixmier, *Traces sur les C*-algèbres*, Ann. Inst. Fourier (Grenoble) 13 (1963),
  219–262. Chapitre I: Définition 2, p. 224; Lemme 3, p. 226.
-/

public section

open scoped ENNReal ComplexOrder

namespace TauCeti

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {τ : B → ℝ≥0∞}

namespace PositiveTracialFunctional

/-- A positive tracial functional is determined by its trace on `B₊`. -/
theorem ext_of_toTrace {ω ω' : PositiveTracialFunctional B}
    (h : ∀ x : B, 0 ≤ x → ω.toTrace x = ω'.toTrace x) : ω = ω' := by
  have hlin : (ω : B →ₗ[ℂ] ℂ) = (ω' : B →ₗ[ℂ] ℂ) :=
    LinearMap.ext_on CStarAlgebra.span_nonneg fun x (hx : 0 ≤ x) ↦ by
      simp only [LinearMap.coe_ofClass, ω.apply_eq_toReal_toTrace hx,
        ω'.apply_eq_toReal_toTrace hx, h x hx]
  exact DFunLike.ext _ _ fun x ↦ LinearMap.congr_fun hlin x

end PositiveTracialFunctional

namespace IsTrace

/-- The **positive tracial functional of a bounded trace**: for a trace `τ` finite on `B₊`, the
linear extension `x ↦ τ(x)` of `τ` to `𝔪_τ = B`. -/
noncomputable def toPositiveTracialFunctional (hτ : IsTrace τ)
    (hfin : ∀ x : B, 0 ≤ x → τ x < ∞) : PositiveTracialFunctional B where
  toPositiveLinearMap := PositiveLinearMap.mk₀
    (hτ.linearMap.comp (LinearMap.id.codRestrict (domain τ) (mem_domain_of_lt_top hfin)))
    fun x hx ↦ by
      -- `LinearMap.codRestrict` sends `x` to `⟨x, _⟩` by definition; Mathlib's
      -- `LinearMap.codRestrict_apply` only describes the coercion to `B`, so we unfold directly.
      change 0 ≤ hτ.linearMap ⟨x, mem_domain_of_lt_top hfin x⟩
      rw [hτ.linearMap_apply_of_mem_finitePart (mem_finitePart.2 ⟨hx, hfin x hx⟩)]
      exact Complex.zero_le_real.2 ENNReal.toReal_nonneg
  map_mul_comm' a b := hτ.linearMap_mul_comm (mem_domain_of_lt_top hfin a) b

/-- The value of `hτ.toPositiveTracialFunctional hfin` is that of the linear extension of `τ`. -/
theorem toPositiveTracialFunctional_apply (hτ : IsTrace τ) (hfin : ∀ x : B, 0 ≤ x → τ x < ∞)
    (x : B) :
    hτ.toPositiveTracialFunctional hfin x = hτ.linearMap ⟨x, mem_domain_of_lt_top hfin x⟩ :=
  (rfl)

/-- On `B₊`, the positive tracial functional of a bounded trace `τ` is `τ`. -/
theorem toPositiveTracialFunctional_apply_of_nonneg (hτ : IsTrace τ)
    (hfin : ∀ x : B, 0 ≤ x → τ x < ∞) {x : B} (hx : 0 ≤ x) :
    hτ.toPositiveTracialFunctional hfin x = ((τ x).toReal : ℂ) := by
  rw [toPositiveTracialFunctional_apply]
  exact hτ.linearMap_apply_of_mem_finitePart (mem_finitePart.2 ⟨hx, hfin x hx⟩)

/-- The trace of the positive tracial functional of a bounded trace `τ` is `τ` on `B₊`. -/
theorem toTrace_toPositiveTracialFunctional_of_nonneg (hτ : IsTrace τ)
    (hfin : ∀ x : B, 0 ≤ x → τ x < ∞) {x : B} (hx : 0 ≤ x) :
    (hτ.toPositiveTracialFunctional hfin).toTrace x = τ x := by
  rw [PositiveTracialFunctional.toTrace_apply,
    hτ.toPositiveTracialFunctional_apply_of_nonneg hfin hx, Complex.ofReal_re,
    ENNReal.ofReal_toReal (hfin x hx).ne]

/-- **Bounded traces**: a trace that is finite on `B₊` is the restriction to `B₊` of a positive
tracial functional. -/
theorem exists_positiveFunctional (hτ : IsTrace τ) (hfin : ∀ x : B, 0 ≤ x → τ x < ∞) :
    ∃ ω : PositiveTracialFunctional B, ∀ x : B, 0 ≤ x → ω.toTrace x = τ x :=
  ⟨hτ.toPositiveTracialFunctional hfin, fun _ ↦ hτ.toTrace_toPositiveTracialFunctional_of_nonneg
    hfin⟩

/-- A trace is finite on `B₊` if and only if it is the restriction to `B₊` of a positive tracial
functional. -/
theorem forall_lt_top_iff_exists_positiveFunctional (hτ : IsTrace τ) :
    (∀ x : B, 0 ≤ x → τ x < ∞) ↔
      ∃ ω : PositiveTracialFunctional B, ∀ x : B, 0 ≤ x → ω.toTrace x = τ x := by
  refine ⟨hτ.exists_positiveFunctional, fun ⟨ω, hω⟩ x hx ↦ ?_⟩
  rw [← hω x hx]
  exact ω.toTrace_lt_top x

/-- Uniqueness: a positive tracial functional whose trace agrees with a bounded trace `τ` on `B₊`
is the positive tracial functional of `τ`. -/
theorem eq_toPositiveTracialFunctional_of_toTrace (hτ : IsTrace τ)
    (hfin : ∀ x : B, 0 ≤ x → τ x < ∞) {ω : PositiveTracialFunctional B}
    (hω : ∀ x : B, 0 ≤ x → ω.toTrace x = τ x) : ω = hτ.toPositiveTracialFunctional hfin :=
  PositiveTracialFunctional.ext_of_toTrace fun x hx ↦ by
    rw [hω x hx, hτ.toTrace_toPositiveTracialFunctional_of_nonneg hfin hx]

end IsTrace

namespace PositiveTracialFunctional

/-- The positive tracial functional of the trace of `ω` is `ω`. -/
@[simp]
theorem toPositiveTracialFunctional_toTrace (ω : PositiveTracialFunctional B) :
    ω.isTrace_toTrace.toPositiveTracialFunctional (fun x _ ↦ ω.toTrace_lt_top x) = ω :=
  (ω.isTrace_toTrace.eq_toPositiveTracialFunctional_of_toTrace _ fun _ _ ↦ rfl).symm

end PositiveTracialFunctional

end TauCeti
