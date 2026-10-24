/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.QuadraticExtension
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Cup.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.StiefelWhitney.LocalHasse

import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Evens.Kummer.Value
import TauCeti.FieldTheory.Separable.Quadratic

/-!
# The relative Stiefel–Whitney formula over a local field

Let `K` be a nonarchimedean local field in which `2` is invertible, for instance a finite
extension of `ℚ₂`, and let `L = K(x)` be a quadratic extension with `x ∉ K` and `x² = d ∈ Kˣ`.
For `a ∈ Lˣ` write `Tr_*⟨a⟩` for the twisted trace form `y ↦ Tr_{L/K}(a y²)`. Over any field in
which `2` is invertible, the relative Stiefel–Whitney formula in degree two reduces, for a
quadratic extension, to

```text
w₂(Tr_*⟨a⟩) = w₂(Tr_*⟨1⟩) + N^{Ev}((a))
```

(`TauCeti.sw2Class_formClass_traceTransfer_smul_sq_eq_add_galoisEvens`). Over `K` the second
Stiefel–Whitney class is determined by the local Hasse invariant
(`TauCeti.sw2Class_eq_iff_localHasse_eq`), so the identity becomes a statement about signs: the
Evens norm of `(a)` vanishes exactly when the twisted and the untwisted trace forms have the same
local Hasse invariant. These invariants are Hilbert symbols:

```text
s(Tr_*⟨1⟩) = (2, d)_K,
s(Tr_*⟨a⟩) = (Tr a, −d · N a)_K    if Tr a ≠ 0,
s(Tr_*⟨a⟩) = 1                     if Tr a = 0.
```

Correspondingly, when `Tr a ≠ 0` the Evens norm `N^{Ev}((a)) = (Tr a) ∪ (−d · N a) + (2) ∪ (d)`
vanishes exactly when `(Tr a, −d · N a)_K = (2, d)_K`. Over a finite extension of `ℚ₂` this
turns both sides of the relative formula into Hilbert-symbol computations, for every `a ∈ Lˣ`.
The degree-one formula `w₁(Tr_*⟨a⟩) = w₁(Tr_*⟨1⟩) + cor (a)` is already an identity of square
classes over every field (`TauCeti.sw1Class_formClass_traceTransfer_smul_sq`).

Fix `c, e ∈ Kˣ` with `(c, e)_K = -1`, so that `κ = (c) ∪ (e)` is a nonzero class. Every Kummer
cup over `K` is a multiple of `κ` (`TauCeti.cup_kummerClass_eq_hilbertSymbol_smul`), so the Evens
norm is known exactly and not only up to its vanishing:

```text
N^{Ev}((a)) = ε((Tr a, −d · N a)_K · (2, d)_K) • κ    if Tr a ≠ 0,
N^{Ev}((a)) = ε((2, d)_K) • κ                        if Tr a = 0,
```

where `ε : {±1} → ZMod 2` sends `+1` to `0` and `-1` to `1`. Together with the Hilbert-symbol
values of `w₂` above, both sides of the degree-two relative formula become multiples of `κ` with
coefficients in `ZMod 2`.

## Main results

* `TauCeti.localHasse_formClass_traceTransfer_sq_of_sq`: `s(Tr_*⟨1⟩) = (2, d)_K`.
* `TauCeti.localHasse_formClass_traceTransfer_smul_sq_of_sq`: for `Tr a ≠ 0`,
  `s(Tr_*⟨a⟩) = (Tr a, −d · N a)_K`.
* `TauCeti.localHasse_formClass_traceTransfer_smul_sq_of_trace_eq_zero`: for `Tr a = 0`,
  `s(Tr_*⟨a⟩) = 1`.
* `TauCeti.galoisEvens_kummerClass_eq_zero_iff_localHasse_eq`: `N^{Ev}((a)) = 0` if and only if
  `s(Tr_*⟨a⟩) = s(Tr_*⟨1⟩)`.
* `TauCeti.galoisEvens_kummerClass_eq_zero_iff_hilbertSymbol_eq`: for `Tr a ≠ 0`,
  `N^{Ev}((a)) = 0` if and only if `(Tr a, −d · N a)_K = (2, d)_K`.
* `TauCeti.galoisEvens_kummerClass_eq_hilbertSymbol_smul`: for `Tr a ≠ 0` and
  `κ = (c) ∪ (e)` with `(c, e)_K = -1`, `N^{Ev}((a)) = ε((Tr a, −d · N a)_K · (2, d)_K) • κ`.
* `TauCeti.galoisEvens_kummerClass_eq_hilbertSymbol_smul_of_trace_eq_zero`: for `Tr a = 0` and
  `κ` as above, `N^{Ev}((a)) = ε((2, d)_K) • κ`.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, Lemme II.2.1 and Théorème 2.
* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676.
* J.-P. Serre, *Local Fields*, GTM 67 (1979), XIV §2, Proposition 5.
-/

public section

namespace TauCeti

open _root_.ContinuousCohomology RegularFormClass

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)] [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- **The local Hasse invariant of the trace form of a quadratic extension**: if `L` is generated
over a local field `K` by a square root `x ∉ K` of `d`, then `s(Tr_*⟨1⟩) = (2, d)_K`. -/
theorem localHasse_formClass_traceTransfer_sq_of_sq (hfin : Module.finrank K L = 2) {x : L}
    {d : Kˣ} (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L (d : K))
    (h1 : ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Nondegenerate) :
    localHasse (formClass _ h1) = hilbertSymbol (unitOfInvertible (2 : K)) d :=
  (sw2Class_eq_cup_kummerClass_iff_localHasse_eq _ _ _).1
    (sw2Class_formClass_traceTransfer_sq_of_sq hfin hx hx2 h1)

/-- **The local Hasse invariant of a twisted trace form**: if `L` is generated over a local field
`K` by a square root `x ∉ K` of `d`, and `a ∈ Lˣ` has nonzero trace `t`, then
`s(Tr_*⟨a⟩) = (t, −d · N a)_K`. -/
theorem localHasse_formClass_traceTransfer_smul_sq_of_sq (hfin : Module.finrank K L = 2) {x : L}
    {d : Kˣ} (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L (d : K))
    (a : Lˣ) {t : Kˣ} (ht : (t : K) = Algebra.trace K L a)
    (ha : (((a : L) • QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Nondegenerate) :
    localHasse (formClass _ ha) = hilbertSymbol t (-(d * Algebra.normUnits K a)) :=
  (sw2Class_eq_cup_kummerClass_iff_localHasse_eq _ _ _).1
    (sw2Class_formClass_traceTransfer_smul_sq_of_sq hfin hx hx2 a ht ha)

/-- The twisted trace form `Tr_*⟨a⟩` of a quadratic extension of a local field has trivial local
Hasse invariant when `Tr a = 0`, since it is then a hyperbolic plane. -/
theorem localHasse_formClass_traceTransfer_smul_sq_of_trace_eq_zero
    (hfin : Module.finrank K L = 2) (a : Lˣ) (htr : Algebra.trace K L a = 0)
    (ha : (((a : L) • QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Nondegenerate) :
    localHasse (formClass _ ha) = 1 :=
  (sw2Class_eq_zero_iff_localHasse_eq_one _).1
    (sw2Class_formClass_traceTransfer_smul_sq_of_trace_eq_zero hfin a htr ha)

variable [Invertible (2 : L)]

/-- **The relative Stiefel–Whitney formula over a local field**: for a quadratic extension `L` of a
local field `K` and `a ∈ Lˣ`, the Evens norm `N^{Ev}((a)) ∈ H²(G_K, 𝔽₂)`, taken along any
`K`-embedding `σ` of `L` into a separable closure of `K`, vanishes exactly when the twisted trace
form `Tr_*⟨a⟩` and the trace form `Tr_*⟨1⟩` have the same local Hasse invariant. -/
theorem galoisEvens_kummerClass_eq_zero_iff_localHasse_eq (σ : L →ₐ[K] SeparableClosure K)
    (hfin : Module.finrank K L = 2) (a : Lˣ)
    (ha : (((a : L) • QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Nondegenerate)
    (h1 : ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Nondegenerate) :
    galoisEvens K L σ hfin (kummerClass a) = 0 ↔
      localHasse (formClass _ ha) = localHasse (formClass _ h1) := by
  rw [← sw2Class_eq_iff_localHasse_eq,
    sw2Class_formClass_traceTransfer_smul_sq_eq_add_galoisEvens σ hfin a ha h1, add_eq_left]

/-- **The Evens norm of a Kummer class over a local field, as Hilbert symbols**: if `L` is
generated over a local field `K` by a square root `x ∉ K` of `d`, and `a ∈ Lˣ` has nonzero trace
`t`, then `N^{Ev}((a)) = (t) ∪ (−d · N a) + (2) ∪ (d)` vanishes exactly when
`(t, −d · N a)_K = (2, d)_K`. -/
theorem galoisEvens_kummerClass_eq_zero_iff_hilbertSymbol_eq (σ : L →ₐ[K] SeparableClosure K)
    (hfin : Module.finrank K L = 2) {x : L} {d : Kˣ} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) (a : Lˣ) {t : Kˣ}
    (ht : (t : K) = Algebra.trace K L a) :
    galoisEvens K L σ hfin (kummerClass a) = 0 ↔
      hilbertSymbol t (-(d * Algebra.normUnits K a)) =
        hilbertSymbol (unitOfInvertible (2 : K)) d := by
  have : Algebra.IsSeparable K L := Algebra.isSeparable_of_finrank_eq_two two_ne_zero hfin
  have hN : Units.map (Algebra.norm K : L →* K) a = Algebra.normUnits K a := Units.ext (by simp)
  -- In `H²(G_K, 𝔽₂)` every class is its own negative, so a sum vanishes exactly when its two
  -- summands agree.
  have hneg : -(trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
      (kummerClass (unitOfInvertible (2 : K))) (kummerClass d) =
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1
          (kummerClass (unitOfInvertible (2 : K))) (kummerClass d) :=
    neg_eq_of_add_eq_zero_right ((two_nsmul _).symm.trans (cohomF2.two_nsmul_eq_zero _ _ _))
  rw [galoisEvens2_kummerClass σ hfin d hx hx2 a t ht, hN, add_eq_zero_iff_eq_neg, hneg,
    cup_kummerClass_eq_cup_kummerClass_iff_hilbertSymbol_eq]

/-- **The Evens norm of a Kummer class over a local field, as an element of `H²(G_K, 𝔽₂)`**: if
`L` is generated over a local field `K` by a square root `x ∉ K` of `d`, and `a ∈ Lˣ` has nonzero
trace `t`, then `N^{Ev}((a)) = ε((t, −d · N a)_K · (2, d)_K) • ((c) ∪ (e))` for all `c, e` with
`(c, e)_K = -1`, where `ε` sends the signs `+1`, `-1` to `0`, `1`. -/
theorem galoisEvens_kummerClass_eq_hilbertSymbol_smul (σ : L →ₐ[K] SeparableClosure K)
    (hfin : Module.finrank K L = 2) {x : L} {d : Kˣ} (hx : x ∉ Set.range (algebraMap K L))
    (hx2 : x ^ 2 = algebraMap K L (d : K)) (a : Lˣ) {t : Kˣ}
    (ht : (t : K) = Algebra.trace K L a) {c e : Kˣ} (hce : hilbertSymbol c e = -1) :
    galoisEvens K L σ hfin (kummerClass a) =
      additiveIntUnitsAddEquiv (Additive.ofMul (hilbertSymbol t (-(d * Algebra.normUnits K a)) *
        hilbertSymbol (unitOfInvertible (2 : K)) d)) •
          (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass c)
            (kummerClass e) := by
  have : Algebra.IsSeparable K L := Algebra.isSeparable_of_finrank_eq_two two_ne_zero hfin
  have hN : Units.map (Algebra.norm K : L →* K) a = Algebra.normUnits K a := Units.ext (by simp)
  rw [galoisEvens2_kummerClass σ hfin d hx hx2 a t ht, hN,
    cup_kummerClass_eq_hilbertSymbol_smul hce t, cup_kummerClass_eq_hilbertSymbol_smul hce _ d,
    ofMul_mul, map_add, add_smul]

/-- **The Evens norm of a trace-zero Kummer class over a local field**: if `L` is generated over a
local field `K` by a square root `x ∉ K` of `d`, and `a ∈ Lˣ` has trace zero, then
`N^{Ev}((a)) = ε((2, d)_K) • ((c) ∪ (e))` for all `c, e` with `(c, e)_K = -1`, where `ε` sends the
signs `+1`, `-1` to `0`, `1`. -/
theorem galoisEvens_kummerClass_eq_hilbertSymbol_smul_of_trace_eq_zero
    (σ : L →ₐ[K] SeparableClosure K) (hfin : Module.finrank K L = 2) {x : L} {d : Kˣ}
    (hx : x ∉ Set.range (algebraMap K L)) (hx2 : x ^ 2 = algebraMap K L (d : K)) (a : Lˣ)
    (htr : Algebra.trace K L a = 0) {c e : Kˣ} (hce : hilbertSymbol c e = -1) :
    galoisEvens K L σ hfin (kummerClass a) =
      additiveIntUnitsAddEquiv (Additive.ofMul (hilbertSymbol (unitOfInvertible (2 : K)) d)) •
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass c) (kummerClass e) := by
  have : Algebra.IsSeparable K L := Algebra.isSeparable_of_finrank_eq_two two_ne_zero hfin
  rw [galoisEvens2_kummerClass_of_trace_eq_zero σ hfin d hx hx2 a htr,
    cup_kummerClass_eq_hilbertSymbol_smul hce _ d]

end TauCeti
