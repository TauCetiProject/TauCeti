/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.IntUnitsPower
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import TauCeti.NumberTheory.LocalField.QuadraticForm.AnisotropicQuaternary

/-!
# Kummer cup products over a local field

Let `K` be a nonarchimedean local field in which `2` is invertible, for instance a finite
extension of `ℚ₂`. Over every field in which `2` is invertible, two Kummer cups
`(a) ∪ (b), (c) ∪ (d) ∈ H²(G_K, 𝔽₂)` agree exactly when the quaternion algebras `(a, b)` and
`(c, d)` have the same Brauer class. Over `K`, quaternion algebras are classified by their Hilbert
symbols, so a Kummer cup is determined by the Hilbert symbol `(a, b)_K`.

In particular, fix `c, e ∈ Kˣ` with `(c, e)_K = -1`, so that `κ = (c) ∪ (e)` is nonzero. Every
Kummer cup is then `ε • κ`, where `ε ∈ ZMod 2` is the Hilbert symbol `(a, b)_K` read additively
(`+1 ↦ 0`, `-1 ↦ 1`). This turns identities between Kummer cups into identities in `ZMod 2`.

## Main results

* `TauCeti.cup_kummerClass_eq_cup_kummerClass_iff_hilbertSymbol_eq`:
  `(a) ∪ (b) = (c) ∪ (d)` if and only if `(a, b)_K = (c, d)_K`.
* `TauCeti.cup_kummerClass_eq_hilbertSymbol_smul`: `(a) ∪ (b) = ε • ((c) ∪ (e))` whenever
  `(c, e)_K = -1`, with `ε` the additive form of `(a, b)_K`.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), XIV §2, Proposition 5.
-/

public section

namespace TauCeti

open _root_.ContinuousCohomology

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-- **Kummer cups over a local field are read off Hilbert symbols**: `(a) ∪ (b) = (c) ∪ (d)` in
`H²(G_K, 𝔽₂)` if and only if `(a, b)_K = (c, d)_K`. -/
theorem cup_kummerClass_eq_cup_kummerClass_iff_hilbertSymbol_eq (a b c d : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) =
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass c) (kummerClass d) ↔
      hilbertSymbol a b = hilbertSymbol c d :=
  (cup_kummerClass_eq_cup_kummerClass_iff_quaternionClass_eq a b c d).trans
    (BrauerGroup.quaternionClass_eq_iff_hilbertSymbol_eq a b c d)

/-- **A Kummer cup over a local field is its Hilbert symbol times a fixed nonzero cup**: if
`(c, e)_K = -1`, then `(a) ∪ (b) = ε • ((c) ∪ (e))`, where `ε ∈ ZMod 2` is `0` if `(a, b)_K = 1`
and `1` if `(a, b)_K = -1`. -/
theorem cup_kummerClass_eq_hilbertSymbol_smul {c e : Kˣ} (hce : hilbertSymbol c e = -1)
    (a b : Kˣ) :
    (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass a) (kummerClass b) =
      additiveIntUnitsAddEquiv (Additive.ofMul (hilbertSymbol a b)) •
        (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 (kummerClass c) (kummerClass e) := by
  rcases Int.units_eq_one_or (hilbertSymbol a b) with hab | hab
  · rw [hab, (cup_kummerClass_eq_zero_iff_hilbertSymbol_eq_one a b).2 hab]
    simp
  · rw [hab, (cup_kummerClass_eq_cup_kummerClass_iff_hilbertSymbol_eq a b c e).2
      (hab.trans hce.symm)]
    simp

end TauCeti
