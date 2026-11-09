/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Minimum
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Niemeier
import Mathlib.Tactic.DeriveFintype

/-!
# The 24 Niemeier lattices

The rank-24 reference table has 24 rows: the 23 rootful rows `TauCeti.RootfulNiemeierType`, whose
lattices `N_r = r.lattice` are glued from their root lattices `R_r` along the Conway--Sloane glue
codes, and one row without roots, the Leech row, whose lattice is `TauCeti.leechLattice`.  This
file collects them into one family `TauCeti.NiemeierType.lattice`, indexed by the 24 rows.  The
lattices of different rows live in different ambient spaces, recorded by
`TauCeti.NiemeierType.Ambient`.

Every lattice of the family is even, unimodular, positive definite and of rank `24`.  Its number of
roots is the displayed root count of the row, and `0` for the Leech row, whose lattice has no
vector of norm `2`; the Leech row is the unique row without roots
(`TauCeti.NiemeierType.vectorsOfNorm_two_lattice_eq_empty_iff`).  For a rootful row the roots span
exactly `R_r` (`TauCeti.RootfulNiemeierType.span_vectorsOfNorm_two_lattice`).

The 24 lattices are pairwise non-isometric (`TauCeti.NiemeierType.nonempty_isometry_lattice_iff`):
an isometry preserves the number of roots, which separates the Leech row from the others, and two
rootful rows are separated by `TauCeti.RootfulNiemeierType.nonempty_isometry_lattice_iff`.  That
every even unimodular positive definite lattice of rank `24` is isometric to one of these is
Niemeier's classification theorem, which is not proved here.

## Main declarations

* `TauCeti.NiemeierType`: the 24 rows, `rootful r` for the 23 rootful rows and `leech`.
* `TauCeti.NiemeierType.lattice`: the lattice of a row.
* `TauCeti.NiemeierType.isEven_lattice`, `isUnimodular_lattice`, `isPosDef_lattice`,
  `finrank_lattice`: every lattice of the family is even, unimodular, positive definite, of
  rank `24`.
* `TauCeti.NiemeierType.representationNumber_lattice_two`: the number of roots of each row.
* `TauCeti.NiemeierType.vectorsOfNorm_two_lattice_eq_empty_iff`: the Leech row is the only row
  without roots.
* `TauCeti.NiemeierType.nonempty_isometry_lattice_iff`: the 24 lattices are pairwise
  non-isometric.

## References

* H.-V. Niemeier, *Definite quadratische Formen der Dimension 24 und Diskriminante 1*, Journal of
  Number Theory 5 (1973).
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 16,
  §1, Table 16.1, and Chapter 18.
-/

public section

namespace TauCeti

open IntegralLattice

/-- The 24 rows of the rank-24 reference table: the 23 rootful rows and the Leech row, the only
row without roots. -/
inductive NiemeierType where
  /-- The rootful row `r`, whose lattice is glued from the root lattice of `r`. -/
  | rootful (r : RootfulNiemeierType)
  /-- The Leech row, whose lattice has no roots. -/
  | leech
  deriving DecidableEq

/-- The rows form an executable finite type. -/
instance : Fintype NiemeierType := derive_fintype% _

namespace NiemeierType

/-- There are exactly 24 rows. -/
@[simp]
theorem card : Fintype.card NiemeierType = 24 := by
  decide

/-- The ambient rational space of the lattice of a row: the coordinate space of the root lattice
`R_r` for a rootful row `r`, and `ℚ^24` for the Leech row. -/
abbrev Ambient : NiemeierType → Type
  | rootful r => ∀ i, Fin (r.componentType i).rank → ℚ
  | leech => Fin 24 → ℚ

/-- The ambient space of every row is a rational coordinate space. -/
instance instAddCommGroupAmbient : ∀ n : NiemeierType, AddCommGroup n.Ambient
  | rootful _ => Pi.addCommGroup
  | leech => Pi.addCommGroup

/-- The ambient space of every row is a rational vector space. -/
instance instModuleAmbient : ∀ n : NiemeierType, Module ℚ n.Ambient
  | rootful _ => Pi.module _ _ _
  | leech => Pi.module _ _ _

/-- **The Niemeier lattice of a row**: the lattice `N_r` glued from the root lattice of a rootful
row `r`, and the Leech lattice for the Leech row. -/
noncomputable def lattice : (n : NiemeierType) → IntegralLattice n.Ambient
  | rootful r => r.lattice
  | leech => leechLattice

/-- The lattice of a rootful row `r` is `N_r`. -/
@[simp]
theorem lattice_rootful (r : RootfulNiemeierType) : (rootful r).lattice = r.lattice :=
  (rfl)

/-- The lattice of the Leech row is the Leech lattice. -/
@[simp]
theorem lattice_leech : leech.lattice = leechLattice :=
  (rfl)

/-- The number of roots displayed for a row: the root count of a rootful row, and `0` for the
Leech row. -/
@[expose] def rootCount : NiemeierType → ℕ
  | rootful r => r.rootCount
  | leech => 0

/-- The displayed root count of a rootful row `r` is that of `r`. -/
@[simp]
theorem rootCount_rootful (r : RootfulNiemeierType) : (rootful r).rootCount = r.rootCount :=
  (rfl)

/-- The Leech row has displayed root count `0`. -/
@[simp]
theorem rootCount_leech : leech.rootCount = 0 :=
  (rfl)

/-- **Only the Leech row has displayed root count `0`.** -/
@[simp]
theorem rootCount_eq_zero_iff {n : NiemeierType} : n.rootCount = 0 ↔ n = leech := by
  revert n
  decide

/-- **The lattice of every row is even.** -/
theorem isEven_lattice : ∀ n : NiemeierType, n.lattice.IsEven
  | rootful r => r.isEven_lattice
  | leech => isEven_leechLattice

/-- **The lattice of every row is unimodular.** -/
theorem isUnimodular_lattice : ∀ n : NiemeierType, n.lattice.IsUnimodular
  | rootful r => r.isUnimodular_lattice
  | leech => isUnimodular_leechLattice

/-- **The lattice of every row is positive definite.** -/
theorem isPosDef_lattice : ∀ n : NiemeierType, n.lattice.IsPosDef
  | rootful r => r.isPosDef_lattice
  | leech => isPosDef_leechLattice

/-- **The lattice of every row has rank `24`.** -/
@[simp]
theorem finrank_lattice : ∀ n : NiemeierType, Module.finrank ℤ n.lattice = 24
  | rootful r => r.finrank_lattice
  | leech => finrank_leechLattice

/-- **The lattice of every row has the displayed number of roots**: the root count of a rootful
row, and no roots for the Leech row. -/
@[simp]
theorem representationNumber_lattice_two :
    ∀ n : NiemeierType, n.lattice.representationNumber 2 = n.rootCount
  | rootful r => r.representationNumber_lattice_two
  | leech => by
    rw [lattice_leech, representationNumber_def, vectorsOfNorm_two_leechLattice, Set.ncard_empty,
      rootCount_leech]

/-- **The Leech row is the only row without roots.** -/
@[simp]
theorem vectorsOfNorm_two_lattice_eq_empty_iff {n : NiemeierType} :
    n.lattice.vectorsOfNorm 2 = ∅ ↔ n = leech := by
  rw [← rootCount_eq_zero_iff, ← representationNumber_lattice_two,
    n.isPosDef_lattice.representationNumber_eq_zero_iff]

/-- **The 24 Niemeier lattices are pairwise non-isometric.**  An isometry preserves the number of
roots, which separates the Leech row from the rootful rows, and two rootful rows are separated by
`TauCeti.RootfulNiemeierType.nonempty_isometry_lattice_iff`. -/
@[simp]
theorem nonempty_isometry_lattice_iff {m n : NiemeierType} :
    Nonempty (Isometry m.lattice n.lattice) ↔ m = n := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ h ▸ ⟨Isometry.refl _⟩⟩
  have hroots := e.representationNumber_eq 2
  rw [representationNumber_lattice_two, representationNumber_lattice_two] at hroots
  have hleech : m = leech ↔ n = leech := by
    rw [← rootCount_eq_zero_iff, ← rootCount_eq_zero_iff, hroots]
  cases m with
  | rootful r =>
    cases n with
    | rootful s => exact congrArg rootful (RootfulNiemeierType.nonempty_isometry_lattice_iff.mp ⟨e⟩)
    | leech => exact nomatch hleech.mpr rfl
  | leech =>
    cases n with
    | rootful s => exact nomatch hleech.mp rfl
    | leech => rfl

end NiemeierType

end TauCeti
