/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.OpenSubgroup
public import TauCeti.FieldTheory.GaloisCohomology.BrauerTorsion

/-!
# Corestriction on local roots-of-unity cohomology

For a nonarchimedean local field `K`, an exponent `n` invertible in `K`, and an open subgroup
`U` of `G_K`, corestriction `H²(U, μₙ) → H²(G_K, μₙ)` is bijective. This is the coefficient
corestriction needed to transport the local Tate-duality pairing through Shapiro's lemma.

The Kummer inclusion identifies both groups with the `n`-torsion in the corresponding Brauer
cohomology groups. Corestriction commutes with that inclusion and is an isomorphism on Brauer
cohomology (`explicitCor2_unitsCoeff_bijective`), so its restriction to `n`-torsion is an
isomorphism too. No coprimality with the subgroup index or the residue characteristic is needed.

The statement uses the explicit low-degree model and the single ambient coefficient module
`KummerCoeff K n`, matching the generic duality and Shapiro API.

## Main result

* `TauCeti.ClassFieldTheory.explicitCor2_kummerCoeff_bijective`: degree-two corestriction on
  roots-of-unity coefficients is bijective for every open subgroup of a local `G_K`.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter II, §5.2, Theorem 2 and its proof.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (6.2.1) and (7.2.6).
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ} (hn : IsUnit (n : K))
  (U : Subgroup (AbsoluteGaloisGroup K)) [U.FiniteIndex]
  (hU : IsOpen (U : Set (AbsoluteGaloisGroup K)))

include hn

/-- Corestriction on local `H²` with roots-of-unity coefficients is bijective for every open
subgroup, for any exponent invertible in the field. This includes all nonzero exponents in
characteristic zero, even when they divide the subgroup index or the residue characteristic. -/
theorem explicitCor2_kummerCoeff_bijective :
    Function.Bijective (explicitCor2 (AbsoluteGaloisGroup K) (KummerCoeff K n) U hU) := by
  exact explicitCor2_kummerCoeff_bijective_of_unitsCoeff_bijective K hn U hU
    (explicitCor2_unitsCoeff_bijective K U hU)

end TauCeti.ClassFieldTheory
