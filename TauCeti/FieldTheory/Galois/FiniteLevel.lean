/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.Galois.Restriction
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

/-- Conditions on restrictions to finite Galois subextensions cut out a closed subgroup in the
Krull topology. No compatibility between the conditions is needed for closedness. -/
theorem isClosed_iInf_comap_restrictNormalHom :
    IsClosed (((⨅ M, (H M).comap
      (AlgEquiv.restrictNormalHom M : Gal(L/K) →* Gal(M/K))) : Subgroup Gal(L/K)) :
      Set Gal(L/K)) := by
  rw [Subgroup.coe_iInf]
  exact isClosed_iInter fun M ↦ (isClosed_discrete _).preimage
    (InfiniteGalois.restrictNormalHom_continuous M.toIntermediateField)

/-- If restriction carries each finite-level subgroup into the subgroup below it, their
pullbacks to `Gal(L/K)` form an antitone family. No surjectivity between subgroups is needed. -/
theorem antitone_comap_restrictNormalHom
    (hH : ∀ ⦃M N : FiniteGaloisIntermediateField K L⦄ (hMN : M ≤ N),
      (H N).map (inclusion ((FiniteGaloisIntermediateField.le_iff M N).mp hMN)).restrictNormalHom ≤
        H M) :
    Antitone (fun M ↦ (H M).comap (AlgEquiv.restrictNormalHom M : Gal(L/K) →* Gal(M/K))) := by
  intro M N hMN σ hσ
  simp only [Subgroup.mem_comap] at hσ ⊢
  apply hH hMN
  refine ⟨AlgEquiv.restrictNormalHom N σ, hσ, ?_⟩
  rw [← IntermediateField.restrictNormalHom_val N.toIntermediateField,
    ← IntermediateField.restrictNormalHom_val M.toIntermediateField,
    AlgHom.restrictNormalHom_restrictNormalHom]
  rfl

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
  let S (N : FiniteGaloisIntermediateField K L) : Subgroup Gal(L/K) :=
    (H N).comap (AlgEquiv.restrictNormalHom N)
  have hanti : Antitone S := antitone_comap_restrictNormalHom H fun _ _ h ↦ (hH h).le
  have hclosed (N : FiniteGaloisIntermediateField K L) : IsClosed (S N : Set Gal(L/K)) :=
    (isClosed_discrete _).preimage
      (InfiniteGalois.restrictNormalHom_continuous N.toIntermediateField)
  rw [MonoidHom.map_iInf_of_isClosed _ (InfiniteGalois.restrictNormalHom_continuous
    M.toIntermediateField) S hclosed (fun N P ↦ ⟨N ⊔ P, hanti le_sup_left, hanti le_sup_right⟩)]
  refine le_antisymm ?_ (le_iInf fun N ↦ ?_)
  · exact (iInf_le _ M).trans_eq
      (Subgroup.map_comap_eq_self_of_surjective (AlgEquiv.restrictNormalHom_surjective L) _)
  · intro τ hτ
    rw [← hH (le_sup_left : M ≤ M ⊔ N)] at hτ
    obtain ⟨ρ, hρ, hρτ⟩ := hτ
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective L ρ
    refine ⟨σ, hanti (le_sup_right : N ≤ M ⊔ N) (by simpa [S, hσ] using hρ), ?_⟩
    rw [← hρτ, ← hσ, ← IntermediateField.restrictNormalHom_val (M ⊔ N).toIntermediateField,
      ← IntermediateField.restrictNormalHom_val M.toIntermediateField,
      AlgHom.restrictNormalHom_restrictNormalHom]
    rfl

end TauCeti
