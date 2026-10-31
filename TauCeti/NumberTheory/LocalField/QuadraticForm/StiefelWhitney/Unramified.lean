/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.QuadraticExtension
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Cup.Unramified

import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Evens.Kummer.Value
import TauCeti.FieldTheory.Separable.Quadratic

/-!
# The trace form of the unramified quadratic extension of a dyadic field

Let `K` be a nonarchimedean local field in which `2` is invertible, and let `Δ ∈ Kˣ` be the
unramified quadratic class: `b ∈ Kˣ` is a norm from `K(√Δ)` exactly when `v_K(b)` is even
(`TauCeti.exists_unramified_class`). Then `L = K(√Δ)` is the unramified quadratic extension of
`K`, and the Hilbert symbol against `Δ` is `(Δ, b)_K = (-1)^{v_K(b)}`
(`TauCeti.hilbertSymbol_unramified`). At `b = 2` this is `TauCeti.hilbertSymbol_two_unramified`:

```text
(2, Δ)_K = (-1)^{v_K(2)}.
```

Over a local field the second Stiefel–Whitney class of the trace form `Tr_*⟨1⟩` of a quadratic
extension `K(√d)` is `(2) ∪ (d)`, and the Evens norm of the Kummer class of `√d` is the same class
(`TauCeti.sw2Class_formClass_traceTransfer_sq_of_sq`, `TauCeti.galoisEvens2_kummerClass_sqrt`).
Fix `c, e ∈ Kˣ` with `(c, e)_K = -1`, so that `κ = (c) ∪ (e)` is nonzero. Every Kummer cup is a
multiple of `κ` (`TauCeti.cup_kummerClass_eq_hilbertSymbol_smul`), and for `L = K(√Δ)` both
classes are

```text
w₂(Tr_*⟨1⟩) = N^{Ev}((√Δ)) = v_K(2) • κ.
```

So they vanish when the residue characteristic is odd, where `v_K(2) = 0`. For a finite extension
`K` of `ℚ₂`, where `v_K(2)` is the absolute ramification index `e` of `K`, they are nonzero exactly
when `e` is odd. Over `ℚ₂` itself, where `e = 1` and `Δ` is the class of `5`, this recovers the
nonzero class `w₂(Tr_*⟨1⟩) = (2) ∪ (5)` of `ℚ₂(√5)`.

## Main results

* `TauCeti.sw2Class_formClass_traceTransfer_sq_unramified`: `w₂(Tr_*⟨1⟩) = v_K(2) • κ` for
  `L = K(√Δ)` and `κ = (c) ∪ (e)` with `(c, e)_K = -1`.
* `TauCeti.galoisEvens_kummerClass_sqrt_unramified`: `N^{Ev}((√Δ)) = v_K(2) • κ`.
* `TauCeti.sw2Class_formClass_traceTransfer_sq_unramified_ne_zero_iff`: over a finite extension
  of `ℚ₂`, `w₂(Tr_*⟨1⟩) ≠ 0` exactly when the absolute ramification index is odd.
* `TauCeti.galoisEvens_kummerClass_sqrt_unramified_ne_zero_iff`: the same criterion for
  `N^{Ev}((√Δ))`.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1.
* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

universe u

namespace TauCeti

open _root_.ContinuousCohomology

variable {K L : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-- A square root of the unramified class does not lie in `K`, since `Δ` is not a square. -/
private theorem not_mem_range_of_sq_eq_unramified [Field L] [Algebra K L] {x : L} {Δ : Kˣ}
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd)
    (hx2 : x ^ 2 = algebraMap K L (Δ : K)) : x ∉ Set.range (algebraMap K L) := by
  rintro ⟨c, rfl⟩
  have hc : c ^ 2 = (Δ : K) := (algebraMap K L).injective (by rw [map_pow, hx2])
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact Δ.ne_zero (by rw [← hc]; ring)
  exact not_isSquare_of_unramified_class (isUnit_of_invertible (2 : K)).ne_zero hΔ
    ⟨Units.mk0 c hc0, Units.ext (by rw [Units.val_mul, Units.val_mk0, ← hc]; ring)⟩

variable [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The trace form of the unramified quadratic extension**: if `L` is generated over a local
field `K` by a square root of the unramified class `Δ`, then
`w₂(Tr_*⟨1⟩) = v_K(2) • ((c) ∪ (e))` for all `c, e` with `(c, e)_K = -1`, where `v_K(2)` is the
dyadic level `TauCeti.dyadicLevel`. -/
theorem sw2Class_formClass_traceTransfer_sq_unramified (hfin : Module.finrank K L = 2) {x : L}
    {Δ : Kˣ} (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd)
    (hx2 : x ^ 2 = algebraMap K L (Δ : K))
    (h1 : ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Nondegenerate)
    {c e : Kˣ} (hce : hilbertSymbol c e = -1) :
    sw2Class (formClass _ h1) =
      (dyadicLevel K (isUnit_of_invertible (2 : K)).ne_zero : ZMod 2) •
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass c) (kummerClass e) := by
  rw [sw2Class_formClass_traceTransfer_sq_of_sq hfin
      (not_mem_range_of_sq_eq_unramified hΔ hx2) hx2 h1,
    cup_kummerClass_eq_hilbertSymbol_smul hce _ Δ, hilbertSymbol_two_unramified hΔ,
    additiveIntUnitsAddEquiv_ofMul_neg_one_pow]

/-- **The Evens norm of the square root of the unramified class**: if `L` is generated over a
local field `K` by a square root `x` of the unramified class `Δ`, then the Evens norm of the
Kummer class of `x`, taken along any `K`-embedding `σ` of `L` into a separable closure of `K`, is
`N^{Ev}((x)) = v_K(2) • ((c) ∪ (e))` for all `c, e` with `(c, e)_K = -1`. -/
theorem galoisEvens_kummerClass_sqrt_unramified [Invertible (2 : L)]
    (σ : L →ₐ[K] SeparableClosure K) (hfin : Module.finrank K L = 2) {x : L} {Δ : Kˣ}
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd)
    (hx2 : x ^ 2 = algebraMap K L (Δ : K)) (b : Lˣ) (hb : (b : L) = x)
    {c e : Kˣ} (hce : hilbertSymbol c e = -1) :
    galoisEvens K L σ hfin (kummerClass b) =
      (dyadicLevel K (isUnit_of_invertible (2 : K)).ne_zero : ZMod 2) •
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass c) (kummerClass e) := by
  have : Algebra.IsSeparable K L := Algebra.isSeparable_of_finrank_eq_two two_ne_zero hfin
  rw [galoisEvens2_kummerClass_sqrt σ hfin Δ (not_mem_range_of_sq_eq_unramified hΔ hx2) hx2 b hb,
    cup_kummerClass_eq_hilbertSymbol_smul hce _ Δ, hilbertSymbol_two_unramified hΔ,
    additiveIntUnitsAddEquiv_ofMul_neg_one_pow]

/-- **The trace form of the unramified quadratic extension of a finite extension of `ℚ₂`**: if
`K` is a finite extension of `ℚ₂` and `L = K(√Δ)` its unramified quadratic extension, then
`w₂(Tr_*⟨1⟩) ≠ 0` exactly when the absolute ramification index of `K` is odd. -/
theorem sw2Class_formClass_traceTransfer_sq_unramified_ne_zero_iff [Fact (Nat.Prime 2)]
    [FinitePadicExtension K 2] (hfin : Module.finrank K L = 2) {x : L} {Δ : Kˣ}
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd)
    (hx2 : x ^ 2 = algebraMap K L (Δ : K))
    (h1 : ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Nondegenerate) :
    sw2Class (formClass _ h1) ≠ 0 ↔ Odd (absoluteRamificationIndex K 2) := by
  rw [sw2Class_formClass_traceTransfer_sq_of_sq hfin
      (not_mem_range_of_sq_eq_unramified hΔ hx2) hx2 h1,
    cup_kummerClass_two_unramified_ne_zero_iff hΔ]

/-- **The Evens norm of the square root of the unramified class over a finite extension of
`ℚ₂`**: if `K` is a finite extension of `ℚ₂` and `L = K(x)` with `x² = Δ` the unramified class,
then `N^{Ev}((x)) ≠ 0` exactly when the absolute ramification index of `K` is odd. -/
theorem galoisEvens_kummerClass_sqrt_unramified_ne_zero_iff [Fact (Nat.Prime 2)]
    [FinitePadicExtension K 2] [Invertible (2 : L)] (σ : L →ₐ[K] SeparableClosure K)
    (hfin : Module.finrank K L = 2) {x : L} {Δ : Kˣ}
    (hΔ : ∀ b : Kˣ, (∃ x y : K, (b : K) = x ^ 2 - Δ * y ^ 2) ↔
      Even (normalizedValuation K b).toAdd)
    (hx2 : x ^ 2 = algebraMap K L (Δ : K)) (b : Lˣ) (hb : (b : L) = x) :
    galoisEvens K L σ hfin (kummerClass b) ≠ 0 ↔ Odd (absoluteRamificationIndex K 2) := by
  have : Algebra.IsSeparable K L := Algebra.isSeparable_of_finrank_eq_two two_ne_zero hfin
  rw [galoisEvens2_kummerClass_sqrt σ hfin Δ (not_mem_range_of_sq_eq_unramified hΔ hx2) hx2 b hb,
    cup_kummerClass_two_unramified_ne_zero_iff hΔ]

end TauCeti
