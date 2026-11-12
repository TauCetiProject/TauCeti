/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.RootSystems
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.CyclicFactors

/-!
# The discriminant groups of the rootful rank-24 root systems

Conway--Sloane's rank-24 table displays, for each of the 23 rootful rows, the discriminant group
`A_R` of the root lattice `R` of the row as a product of cyclic groups, such as `ℤ/18 × ℤ/2` for
`A₁₇ E₇` or `(ℤ/10)² × (ℤ/2)²` for `A₉² D₆`.  This file transcribes these presentations as the
lists of factor orders `TauCeti.RootfulNiemeierType.discriminantFactors`, independently of the
component lists, and proves that the discriminant group of the orthogonal sum of the component
root lattices of every row is additively equivalent to the displayed product
(`TauCeti.RootfulNiemeierType.nonempty_addEquiv_discriminantGroup`).

The transcription is checked by evaluation against the cyclic factors of the ordered components
(`TauCeti.RootfulNiemeierType.discriminantFactors_eq`), so a displayed presentation that
disagreed with the components, for instance one treating an even-rank `Dₙ` alphabet as `ℤ/4`, is
rejected by this check.  The products are group structures: `(ℤ/2)⁴` is the list `[2, 2, 2, 2]`,
and is not identified with any other group of order sixteen.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed.,
  Chapter 16, Table 16.1.
* J. H. Conway and N. J. A. Sloane, *On the enumeration of lattices of determinant one*,
  Journal of Number Theory 15 (1982), Table V.
-/

public section

namespace TauCeti.RootfulNiemeierType

open IntegralLattice

/-- The displayed presentation of the discriminant group of a row's root system, as the orders
of its cyclic factors in the source's order; `[]` is the trivial group of `E₈³`. -/
@[expose] def discriminantFactors : RootfulNiemeierType → List ℕ
  | .d24 => [2, 2]
  | .d16e8 => [2, 2]
  | .e8Cubed => []
  | .a24 => [25]
  | .d12Squared => List.replicate 4 2
  | .a17e7 => [18, 2]
  | .d10e7Squared => List.replicate 4 2
  | .a15d9 => [16, 4]
  | .d8Cubed => List.replicate 6 2
  | .a12Squared => List.replicate 2 13
  | .a11d7e6 => [12, 4, 3]
  | .e6Fourth => List.replicate 4 3
  | .a9SquaredD6 => List.replicate 2 10 ++ List.replicate 2 2
  | .d6Fourth => List.replicate 8 2
  | .a8Cubed => List.replicate 3 9
  | .a7SquaredD5Squared => List.replicate 2 8 ++ List.replicate 2 4
  | .a6Fourth => List.replicate 4 7
  | .a5FourthD4 => List.replicate 4 6 ++ List.replicate 2 2
  | .d4Sixth => List.replicate 12 2
  | .a4Sixth => List.replicate 6 5
  | .a3Eighth => List.replicate 8 4
  | .a2Twelfth => List.replicate 12 3
  | .a1TwentyFourth => List.replicate 24 2

/-- The displayed presentation of every row consists of the cyclic factors of its ordered
components, concatenated in the component order. -/
theorem discriminantFactors_eq (r : RootfulNiemeierType) :
    r.discriminantFactors =
      (List.ofFn fun i : Fin r.components.length ↦
        r.components[i].1.glueCyclicFactors).flatten := by
  cases r <;> decide

/-- **The displayed discriminant groups.**  For every rootful row, the discriminant group of the
orthogonal sum of the root lattices of its ordered components is additively equivalent to the
displayed product of cyclic groups `∏ ℤ/dₖ`, where `d = r.discriminantFactors`. -/
theorem nonempty_addEquiv_discriminantGroup (r : RootfulNiemeierType) :
    Nonempty ((pi fun i : Fin r.components.length ↦
        r.components[i].1.rootLattice r.components[i].2.2).DiscriminantGroup ≃+
      ((k : Fin r.discriminantFactors.length) → ZMod r.discriminantFactors[k])) :=
  DynkinType.nonempty_addEquiv_discriminantGroup_pi_rootLattice _ _ (fun i ↦ r.components[i].2.1)
    (discriminantFactors_eq r).symm

end TauCeti.RootfulNiemeierType
