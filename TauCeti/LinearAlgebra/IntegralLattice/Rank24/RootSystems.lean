/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.ComponentList
public import TauCeti.LinearAlgebra.RootSystem.NumberOfRoots
import Mathlib.Tactic.DeriveFintype

/-!
# The 23 rootful rank-24 component lists

This file records the ordered ADE component lists, displayed Coxeter numbers and root counts
of Conway--Sloane's rootful rank-24 table. The order fixes the coordinate positions for glue
words. Each list uses `DynkinType.Component`, so it can be passed directly to
`DynkinType.componentAlphabet` and `DynkinType.componentSumLattice`. The same components, indexed
by their positions, form the family `RootfulNiemeierType.componentType` of Dynkin types.

The uniform checks establish total rank 24, the displayed root counts from the existing
`DynkinType.numRoots`, and the numerical identity `numRoots = rank * h` for every component.
The displayed component multisets are pairwise distinct. These are facts about the finite
root-system descriptions; no overlattices or classification of lattices are asserted here.

The data definitions are exposed to support proof-producing finite computation. In particular,
the ordered lists must compute when used in the dependent carriers of the component alphabets
and orthogonal sums.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed.,
  Chapter 16, Table 16.1.
* J. H. Conway and N. J. A. Sloane, *On the enumeration of lattices of determinant one*,
  Journal of Number Theory 15 (1982), Table V.
-/

public section

namespace TauCeti

/-- The rootful rows of the Conway--Sloane rank-24 table, in descending root-count order. -/
inductive RootfulNiemeierType where
  /-- `D₂₄`. -/
  | d24
  /-- `D₁₆ E₈`. -/
  | d16e8
  /-- `E₈³`. -/
  | e8Cubed
  /-- `A₂₄`. -/
  | a24
  /-- `D₁₂²`. -/
  | d12Squared
  /-- `A₁₇ E₇`. -/
  | a17e7
  /-- `D₁₀ E₇²`. -/
  | d10e7Squared
  /-- `A₁₅ D₉`. -/
  | a15d9
  /-- `D₈³`. -/
  | d8Cubed
  /-- `A₁₂²`. -/
  | a12Squared
  /-- `A₁₁ D₇ E₆`. -/
  | a11d7e6
  /-- `E₆⁴`. -/
  | e6Fourth
  /-- `A₉² D₆`. -/
  | a9SquaredD6
  /-- `D₆⁴`. -/
  | d6Fourth
  /-- `A₈³`. -/
  | a8Cubed
  /-- `A₇² D₅²`. -/
  | a7SquaredD5Squared
  /-- `A₆⁴`. -/
  | a6Fourth
  /-- `A₅⁴ D₄`. -/
  | a5FourthD4
  /-- `D₄⁶`. -/
  | d4Sixth
  /-- `A₄⁶`. -/
  | a4Sixth
  /-- `A₃⁸`. -/
  | a3Eighth
  /-- `A₂¹²`. -/
  | a2Twelfth
  /-- `A₁²⁴`. -/
  | a1TwentyFourth
  deriving DecidableEq

/-- The row indices form an executable finite type. -/
instance : Fintype RootfulNiemeierType := derive_fintype% _

namespace RootfulNiemeierType

/-- The zero-based source index. Adding one gives the printed row number, from 1 to 23. -/
@[expose] def sourceIndex : RootfulNiemeierType → Fin 23
  | .d24 => 0
  | .d16e8 => 1
  | .e8Cubed => 2
  | .a24 => 3
  | .d12Squared => 4
  | .a17e7 => 5
  | .d10e7Squared => 6
  | .a15d9 => 7
  | .d8Cubed => 8
  | .a12Squared => 9
  | .a11d7e6 => 10
  | .e6Fourth => 11
  | .a9SquaredD6 => 12
  | .d6Fourth => 13
  | .a8Cubed => 14
  | .a7SquaredD5Squared => 15
  | .a6Fourth => 16
  | .a5FourthD4 => 17
  | .d4Sixth => 18
  | .a4Sixth => 19
  | .a3Eighth => 20
  | .a2Twelfth => 21
  | .a1TwentyFourth => 22

/-- The row identifiers enumerate all 23 source positions without repetition. -/
theorem sourceIndex_bijective : Function.Bijective sourceIndex := by decide

/-- There are exactly 23 rootful rows. -/
@[simp] theorem card : Fintype.card RootfulNiemeierType = 23 := by
  simpa using Fintype.card_of_bijective sourceIndex_bijective

/-- The ADE components, in the source's glue-coordinate order. -/
@[expose] def components : RootfulNiemeierType → List DynkinType.Component
  | .d24 => [⟨.D 24, by decide⟩]
  | .d16e8 => [⟨.D 16, by decide⟩, ⟨.E8, by decide⟩]
  | .e8Cubed => List.replicate 3 ⟨.E8, by decide⟩
  | .a24 => [⟨.A 24, by decide⟩]
  | .d12Squared => List.replicate 2 ⟨.D 12, by decide⟩
  | .a17e7 => [⟨.A 17, by decide⟩, ⟨.E7, by decide⟩]
  | .d10e7Squared => ⟨.D 10, by decide⟩ :: List.replicate 2 ⟨.E7, by decide⟩
  | .a15d9 => [⟨.A 15, by decide⟩, ⟨.D 9, by decide⟩]
  | .d8Cubed => List.replicate 3 ⟨.D 8, by decide⟩
  | .a12Squared => List.replicate 2 ⟨.A 12, by decide⟩
  | .a11d7e6 => [⟨.A 11, by decide⟩, ⟨.D 7, by decide⟩, ⟨.E6, by decide⟩]
  | .e6Fourth => List.replicate 4 ⟨.E6, by decide⟩
  | .a9SquaredD6 => List.replicate 2 ⟨.A 9, by decide⟩ ++ [⟨.D 6, by decide⟩]
  | .d6Fourth => List.replicate 4 ⟨.D 6, by decide⟩
  | .a8Cubed => List.replicate 3 ⟨.A 8, by decide⟩
  | .a7SquaredD5Squared =>
      List.replicate 2 ⟨.A 7, by decide⟩ ++ List.replicate 2 ⟨.D 5, by decide⟩
  | .a6Fourth => List.replicate 4 ⟨.A 6, by decide⟩
  | .a5FourthD4 => List.replicate 4 ⟨.A 5, by decide⟩ ++ [⟨.D 4, by decide⟩]
  | .d4Sixth => List.replicate 6 ⟨.D 4, by decide⟩
  | .a4Sixth => List.replicate 6 ⟨.A 4, by decide⟩
  | .a3Eighth => List.replicate 8 ⟨.A 3, by decide⟩
  | .a2Twelfth => List.replicate 12 ⟨.A 2, by decide⟩
  | .a1TwentyFourth => List.replicate 24 ⟨.A 1, by decide⟩

/-- The common Coxeter number displayed in the source. The numerical relation with component
ranks and root counts is checked by `numRoots_eq_rank_mul_coxeterNumber`. -/
@[expose] def coxeterNumber : RootfulNiemeierType → ℕ
  | .d24 => 46
  | .d16e8 | .e8Cubed => 30
  | .a24 => 25
  | .d12Squared => 22
  | .a17e7 | .d10e7Squared => 18
  | .a15d9 => 16
  | .d8Cubed => 14
  | .a12Squared => 13
  | .a11d7e6 | .e6Fourth => 12
  | .a9SquaredD6 | .d6Fourth => 10
  | .a8Cubed => 9
  | .a7SquaredD5Squared => 8
  | .a6Fourth => 7
  | .a5FourthD4 | .d4Sixth => 6
  | .a4Sixth => 5
  | .a3Eighth => 4
  | .a2Twelfth => 3
  | .a1TwentyFourth => 2

/-- The root count displayed in the source, independently of the component root-count sum. -/
@[expose] def rootCount : RootfulNiemeierType → ℕ
  | .d24 => 1104
  | .d16e8 | .e8Cubed => 720
  | .a24 => 600
  | .d12Squared => 528
  | .a17e7 | .d10e7Squared => 432
  | .a15d9 => 384
  | .d8Cubed => 336
  | .a12Squared => 312
  | .a11d7e6 | .e6Fourth => 288
  | .a9SquaredD6 | .d6Fourth => 240
  | .a8Cubed => 216
  | .a7SquaredD5Squared => 192
  | .a6Fourth => 168
  | .a5FourthD4 | .d4Sixth => 144
  | .a4Sixth => 120
  | .a3Eighth => 96
  | .a2Twelfth => 72
  | .a1TwentyFourth => 48

/-- Every displayed component list has total rank 24. -/
@[simp] theorem sum_rank_components (r : RootfulNiemeierType) :
    (r.components.map DynkinType.Component.rank).sum = 24 := by
  cases r <;> decide

/-- The component root-count sum agrees with the independently transcribed source count. -/
@[simp] theorem sum_numRoots_components (r : RootfulNiemeierType) :
    (r.components.unattach.map DynkinType.numRoots).sum = r.rootCount := by
  cases r <;> decide

/-- Every component's root count is its rank times the displayed common Coxeter number. -/
theorem numRoots_eq_rank_mul_coxeterNumber (r : RootfulNiemeierType) :
    ∀ c ∈ r.components, c.1.numRoots = c.rank * r.coxeterNumber := by
  cases r <;> decide

/-- The 23 displayed root systems remain distinct after forgetting component order. -/
theorem components_multiset_injective :
    Function.Injective (fun r : RootfulNiemeierType ↦
      (r.components : Multiset DynkinType.Component)) := by
  -- Rank and root count together already distinguish these component multisets.
  have hinj : Function.Injective (fun r : RootfulNiemeierType ↦
      (r.components.map fun c ↦ (c.rank, c.1.numRoots) : Multiset (ℕ × ℕ))) := by decide
  intro r s h
  exact hinj (by
    simpa only [Multiset.map_coe] using
      congrArg (Multiset.map fun c : DynkinType.Component ↦ (c.rank, c.1.numRoots)) h)

/-- The ADE components of a row as a family indexed by their positions. -/
@[expose] def componentType (r : RootfulNiemeierType) (i : Fin r.components.length) :
    DynkinType :=
  r.components[i].1

/-- The components of a row are simply laced. -/
theorem isSimplyLaced_componentType (r : RootfulNiemeierType) (i : Fin r.components.length) :
    (r.componentType i).IsSimplyLaced :=
  r.components[i].2.2

/-- The components of a row are valid Dynkin types. -/
theorem valid_componentType (r : RootfulNiemeierType) (i : Fin r.components.length) :
    (r.componentType i).Valid :=
  r.components[i].2.1

end RootfulNiemeierType

end TauCeti
