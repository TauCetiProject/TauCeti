/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.KummerLayer
public import TauCeti.NumberTheory.NumberField.Units.SUnit.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The Kummer layer of the `S`-units

Let `K` be a number field containing the `n`-th roots of unity and `S` a finite set of finite
places of `K`. The `S`-units `U_S` (Mathlib's `Set.unit`) have finite image in `Kˣ ⧸ (Kˣ)ⁿ`, so
they have a Kummer layer `kummerLayer n (S.unit K)` in the absolute Galois group `G_K`. By the
general results on Kummer layers it is an abelian layer cutting out `K(U_S^{1/n})`. This file
computes its degree: by Dirichlet's `S`-unit theorem, `U_S` is the product of the roots of unity
and a free abelian group of rank `r₁ + r₂ - 1 + #S`, so the degree is `n ^ (r₁ + r₂ + #S)`.

For `n = p` prime this is the extension `K(U_S^{1/p})` of Milne's proof of global existence, whose
norm subgroup is the image of the Kummer idele subgroup, and of the Kummer case of the second
fundamental inequality.

## Main results

* `TauCeti.ClassFieldTheory.degree_kummerLayer_sUnits`: the Kummer layer of the `S`-units has
  degree `n ^ (r₁ + r₂ + #S)`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §§5 and 9.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

/-- **The degree of the Kummer layer of the `S`-units**: for a number field `K` containing the
`n`-th roots of unity and a finite set `S` of finite places, `[K(U_S^{1/n}) : K] = n ^ (r₁ + r₂ +
#S)`, where `r₁ + r₂` is the number of infinite places of `K`. -/
theorem degree_kummerLayer_sUnits (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity K n] :
    (NormalLayer.ofOpenNormal (kummerLayer n (S.unit K))).degree =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  rw [degree_kummerLayer, relIndex_range_powMonoidHom_sUnits_numberField]

end TauCeti.ClassFieldTheory
