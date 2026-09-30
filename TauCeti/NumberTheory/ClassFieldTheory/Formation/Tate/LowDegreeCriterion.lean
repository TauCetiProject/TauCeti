/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Formation.Tate.DegreeZero
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.TateCohomology.LowDegree

/-!
# Low-degree tests for cup product with a fundamental class

The cup-product criterion for Tate's theorem tests three adjacent degrees. Degree zero is the
cyclicity calculation in `Formation.Tate.DegreeZero`. In degree `-1`, both sides vanish when the
coefficient module has vanishing first cohomology: the source is Tate cohomology of the trivial
integral representation, and the target is ordinary first cohomology. In degree `1`, the source
vanishes for every finite group because it is `H¹(G, ℤ)`.

Together with the degree-zero result, these give the low-degree tests for the cup map attached
to the fundamental class of a class formation. The vanishing of `H¹(G, ℤ)` follows from the
standard description as homomorphisms from a finite group to the torsion-free group `ℤ`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Preliminaries §2, Theorem A; Chapter XIV §4.
-/

public noncomputable section

open CategoryTheory Limits Rep

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- If `H¹` of a finite normal layer vanishes, cupping with any degree-two class is bijective
from degree `-1` to degree `1`, since both Tate groups are zero. -/
theorem cupClass_neg_one_bijective (F : Formation G) (L : NormalLayer G) (u : L.H F 2)
    (h1 : Subsingleton (L.H F 1)) : Function.Bijective (cupClass F L u (-1)) := by
  have : Subsingleton (L.H F 1) := h1
  have : Subsingleton (L.TrivialTateH (-1)) :=
    TauCeti.TateCohomology.subsingleton_tateCohomology_negOne_trivial_int L.Gal
  have : Subsingleton (L.TateH F 1) :=
    Function.Injective.subsingleton (L.tateHIsoH F 1).toLinearEquiv.injective
  have : Subsingleton (L.TateH F (-1 + 2)) := by simpa using
    (inferInstance : Subsingleton (L.TateH F 1))
  exact Function.bijective_of_subsingleton' _

/-- Cupping with any degree-two class is injective in degree `1`: the source is
`H¹(Gal(K/F), ℤ) = 0`. -/
theorem cupClass_one_injective (F : Formation G) (L : NormalLayer G) (u : L.H F 2) :
    Function.Injective (cupClass F L u 1) := by
  have hz : IsZero (L.TrivialTateH 1) :=
    (TauCeti.groupCohomology.isZero_H1_of_isTrivial
      (Rep.trivial ℤ L.Gal ℤ)).of_iso
      ((TateCohomology.isoGroupCohomology 1).app (Rep.trivial ℤ L.Gal ℤ))
  have : Subsingleton (L.TrivialTateH 1) := ModuleCat.subsingleton_of_isZero hz
  exact Function.injective_of_subsingleton _

namespace ClassFormation

variable {F : Formation G}

/-- In degree `-1`, cup product with the fundamental class is bijective. This is the
vanishing-side test of Tate's cup-product criterion for a class formation. -/
theorem cupFundamentalClass_neg_one_bijective (cf : ClassFormation F) (L : NormalLayer G) :
    Function.Bijective (cf.cupFundamentalClass L (-1)) := by
  have heq : cf.cupFundamentalClass L (-1) =
      cupClass F L (cf.fundamentalClass L) (-1) := by
    ext x
    exact cf.cupFundamentalClass_apply L (-1) x
  rw [heq]
  exact cupClass_neg_one_bijective F L (cf.fundamentalClass L) (cf.subsingleton_h1 L)

/-- In degree `1`, cup product with the fundamental class is injective since
`H¹(Gal(K/F), ℤ) = 0`. -/
theorem cupFundamentalClass_one_injective (cf : ClassFormation F) (L : NormalLayer G) :
    Function.Injective (cf.cupFundamentalClass L 1) := by
  have heq : cf.cupFundamentalClass L 1 =
      cupClass F L (cf.fundamentalClass L) 1 := by
    ext x
    exact cf.cupFundamentalClass_apply L 1 x
  rw [heq]
  exact cupClass_one_injective F L (cf.fundamentalClass L)

end ClassFormation

end TauCeti.ClassFieldTheory
