/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.Topology.Algebra.Group.DirectedIntersection

/-!
# Subgroups specified at finite Galois levels

Let `L / K` be a normal extension, and choose a subgroup `H M` of `Gal(M/K)` for each finite
Galois intermediate field `M`. If restriction carries `H N` onto `H M` whenever `M ≤ N`, then
the subgroup of `Gal(L/K)` cut out by all these conditions maps onto every `H M`.

This is the inverse-limit surjectivity argument for upper ramification groups: finite-level
quotient compatibility supplies the hypothesis, and compactness supplies simultaneous lifts.
The argument concerns the Krull topology alone and needs no valuation. Normal extensions may
have inseparable elements, so compactness is taken from restriction to the separable closure.

## Main results

* `TauCeti.map_restrictNormalHom_iInf_comap`: compatible finite-level subgroups are exactly the
  finite images of the subgroup they cut out.
* `TauCeti.isClosed_iInf_comap_restrictNormalHom`: the subgroup cut out by any finite-level
  conditions is closed.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §3, Proposition 14, for the passage from finite
  quotient compatibility to the upper filtration of an infinite Galois group.
* The finite-level lifting argument generalizes
  `TauCeti.map_restrictNormalHom_localAbsoluteUpperRamificationGroup_finiteGalois`.
-/

public section

open IntermediateField

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (H : ∀ M : FiniteGaloisIntermediateField K L, Subgroup (M ≃ₐ[K] M))

/-- A subgroup condition at a finite Galois level has closed pullback in the Krull topology. -/
theorem _root_.FiniteGaloisIntermediateField.isClosed_comap_restrictNormalHom
    (M : FiniteGaloisIntermediateField K L) (S : Subgroup Gal(M/K)) :
    IsClosed (S.comap (AlgEquiv.restrictNormalHom M : Gal(L/K) →* Gal(M/K)) :
      Set Gal(L/K)) :=
  (isClosed_discrete _).preimage
    (InfiniteGalois.restrictNormalHom_continuous M.toIntermediateField)

/-- Conditions on restrictions to finite Galois subextensions cut out a closed subgroup in the
Krull topology. No compatibility between the conditions is needed for closedness. -/
theorem isClosed_iInf_comap_restrictNormalHom :
    IsClosed (((⨅ M, (H M).comap
      (AlgEquiv.restrictNormalHom M : Gal(L/K) →* Gal(M/K))) : Subgroup Gal(L/K)) :
      Set Gal(L/K)) := by
  rw [Subgroup.coe_iInf]
  exact isClosed_iInter fun M ↦ M.isClosed_comap_restrictNormalHom (H M)

/-- If restriction carries each finite-level subgroup into the subgroup below it, their
pullbacks to `Gal(L/K)` form an antitone family. No surjectivity between subgroups is needed. -/
theorem antitone_comap_restrictNormalHom
    (hH : ∀ ⦃M N : FiniteGaloisIntermediateField K L⦄ (hMN : M ≤ N),
      (H N).map (inclusion ((FiniteGaloisIntermediateField.le_iff M N).mp hMN)).restrictNormalHom ≤
        H M) :
    Antitone (fun M ↦ (H M).comap (AlgEquiv.restrictNormalHom M : Gal(L/K) →* Gal(M/K))) :=
  antitone_comap_of_map_le (ι := FiniteGaloisIntermediateField K L)
    (fun M ↦ AlgEquiv.restrictNormalHom M)
    (fun {_ _} h ↦ (inclusion ((FiniteGaloisIntermediateField.le_iff _ _).mp h)).restrictNormalHom)
    H (fun _ _ h ↦ MonoidHom.ext (IntermediateField.restrictNormalHom_inclusion
      ((FiniteGaloisIntermediateField.le_iff _ _).mp h))) hH

/-- In a normal extension, every compatible family of subgroups of the finite Galois groups
is realized by its intersection of pullbacks: restriction from that intersection surjects onto
each prescribed finite-level subgroup. This applies in particular to an algebraic closure over
an imperfect field. -/
theorem map_restrictNormalHom_iInf_comap [Normal K L]
    (hH : ∀ ⦃M N : FiniteGaloisIntermediateField K L⦄ (hMN : M ≤ N),
      (H N).map (inclusion ((FiniteGaloisIntermediateField.le_iff M N).mp hMN)).restrictNormalHom =
        H M)
    (M : FiniteGaloisIntermediateField K L) :
    (⨅ N, (H N).comap (AlgEquiv.restrictNormalHom N : Gal(L/K) →* Gal(N/K))).map
        (AlgEquiv.restrictNormalHom M) = H M := by
  refine map_iInf_comap_of_compatible (ι := FiniteGaloisIntermediateField K L)
    (fun N ↦ AlgEquiv.restrictNormalHom N)
    (fun {_ _} h ↦ (inclusion ((FiniteGaloisIntermediateField.le_iff _ _).mp h)).restrictNormalHom)
    H (fun N ↦ InfiniteGalois.restrictNormalHom_continuous N.toIntermediateField)
    (fun _ ↦ AlgEquiv.restrictNormalHom_surjective L)
    (fun N ↦ N.isClosed_comap_restrictNormalHom (H N)) ?_ hH M
  intro N P h
  exact MonoidHom.ext fun σ ↦ IntermediateField.restrictNormalHom_inclusion _ σ

end TauCeti
