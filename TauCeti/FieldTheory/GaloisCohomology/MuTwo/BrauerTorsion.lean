/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.BrauerTorsion
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic

/-!
# Mod-two classes in the cohomological Brauer group

Let `K` be a field in which `2` is invertible. The coefficient identification
`TauCeti.kummerCoeffIsoTrivialF2` transports the Kummer-sequence map

```text
H²(G_K, μ₂) → H²(G_K, (Kˢ)ˣ)
```

to a map from cohomology with trivial `𝔽₂` coefficients. This file names that transported map
as `TauCeti.h2MuToUnits` and records the two properties inherited from the Kummer sequence: it
is injective, and its image is exactly the `2`-torsion of the cohomology with multiplicative
coefficients.

The comparison theorem `TauCeti.kummerCoeffIsoTrivialF2_hom_comp_h2MuToUnits` characterizes the
transport: moving a `μ₂`-class to trivial `𝔽₂` coefficients and then applying
`TauCeti.h2MuToUnits` is the original map `TauCeti.h2KummerToUnits` at `n = 2`.

## Main definitions

* `TauCeti.h2MuToUnits`: the map from `H²(G_K, 𝔽₂)` to cohomology with multiplicative
  coefficients.

## Main results

* `TauCeti.h2MuToUnits_injective`: the map is injective.
* `TauCeti.h2MuToUnits_range`: its image is the `2`-torsion.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.1) and the exact sequence following it.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (K : Type u) [Field K] [Invertible (2 : K)]

/-- **The map from `H²(G_K, 𝔽₂)` to cohomology with multiplicative coefficients.** It is
the Kummer-sequence map `TauCeti.h2KummerToUnits` at `n = 2`, precomposed with the inverse of the
image of the coefficient identification `TauCeti.kummerCoeffIsoTrivialF2` under the
continuous-cohomology functor `TauCeti.ContinuousCohomology.continuousCohomologyFunctor`. -/
noncomputable def h2MuToUnits :
    continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K)) ⟶
      continuousCohomology 2
        (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K)) :=
  ((ContinuousCohomology.continuousCohomologyFunctor ℤ (AbsoluteGaloisGroup K) 2).mapIso
    (kummerCoeffIsoTrivialF2 K)).inv ≫ h2KummerToUnits K 2

/-- Transporting a `μ₂`-class to trivial `𝔽₂` coefficients before applying
`TauCeti.h2MuToUnits` recovers the Kummer-sequence map at `n = 2`. This equation characterizes
the coefficient transport used in `TauCeti.h2MuToUnits`. -/
@[simp, reassoc (attr := simp)]
theorem kummerCoeffIsoTrivialF2_hom_comp_h2MuToUnits :
    ContinuousCohomology.coeffMap (kummerCoeffIsoTrivialF2 K).hom 2 ≫ h2MuToUnits K =
      h2KummerToUnits K 2 :=
  Iso.hom_inv_id_assoc
    ((ContinuousCohomology.continuousCohomologyFunctor ℤ (AbsoluteGaloisGroup K) 2).mapIso
      (kummerCoeffIsoTrivialF2 K)) _

/-- **The map `H²(G_K, 𝔽₂) → H²(G_K, (Kˢ)ˣ)` is injective.** -/
theorem h2MuToUnits_injective : Function.Injective (h2MuToUnits K).hom :=
  (h2KummerToUnits_injective (K := K) (n := 2) (isUnit_of_invertible (2 : K))).comp
    ((ContinuousCohomology.continuousCohomologyFunctor ℤ (AbsoluteGaloisGroup K) 2).mapIso
      (kummerCoeffIsoTrivialF2 K)).symm.toContinuousLinearEquiv.injective

/-- **The image of `H²(G_K, 𝔽₂)` in `H²(G_K, (Kˢ)ˣ)` is the `2`-torsion.** -/
@[simp]
theorem h2MuToUnits_range
    (x : continuousCohomology 2
      (ofDiscreteModule ℤ (AbsoluteGaloisGroup K) (UnitsCoeff K))) :
    (∃ y, (h2MuToUnits K).hom y = x) ↔ x + x = 0 := by
  rw [← two_nsmul, ← h2KummerToUnits_range (K := K) (n := 2) (isUnit_of_invertible (2 : K))]
  -- `TauCeti.h2MuToUnits` is by definition the inverse coefficient transport followed by
  -- `h2KummerToUnits K 2`, and precomposing with a surjection does not change the range.
  exact (((ContinuousCohomology.continuousCohomologyFunctor ℤ (AbsoluteGaloisGroup K) 2).mapIso
    (kummerCoeffIsoTrivialF2 K)).symm.toContinuousLinearEquiv.surjective.exists
      (p := fun z ↦ (h2KummerToUnits K 2).hom z = x)).symm

end TauCeti
