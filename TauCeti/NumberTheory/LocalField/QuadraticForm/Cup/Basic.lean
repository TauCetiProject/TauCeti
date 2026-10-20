/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import TauCeti.NumberTheory.LocalField.QuadraticForm.AnisotropicQuaternary

/-!
# Kummer cup products over a local field

Let `K` be a nonarchimedean local field in which `2` is invertible, for instance a finite
extension of `ℚ₂`. Over every field in which `2` is invertible, two Kummer cups
`(a) ∪ (b), (c) ∪ (d) ∈ H²(G_K, 𝔽₂)` agree exactly when the quaternion algebras `(a, b)` and
`(c, d)` have the same Brauer class. Over `K`, quaternion algebras are classified by their Hilbert
symbols, so a Kummer cup is determined by the Hilbert symbol `(a, b)_K`.

## Main results

* `TauCeti.cup_kummerClass_eq_cup_kummerClass_iff_hilbertSymbol_eq`:
  `(a) ∪ (b) = (c) ∪ (d)` if and only if `(a, b)_K = (c, d)_K`.

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

end TauCeti
