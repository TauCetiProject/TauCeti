/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Weights
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import Mathlib.GroupTheory.Solvable
import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin

/-!
# Scalar action of connected normal solvable subgroups

A connected reduced solvable closed subgroup of a reduced connected affine group acts by
scalars on each finite-dimensional simple rational representation, provided it is normal.
Lie--Kolchin supplies a joint eigenvector for the subgroup. The ambient group's connectedness
makes its joint weight space invariant, and simplicity makes that space the whole representation.
This is the representation-theoretic step in eliminating solvable radicals of classical groups.

The proof combines `Comodule.hasNonzeroWeightVector_of_isSolvable` with
`Comodule.normalWeightSubcomodule`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§17.6 and 19.
* A. Borel, *Linear Algebraic Groups*, §10.5.
-/

public section

namespace TauCeti.HopfIdeal

open WithConv

noncomputable section

variable {k H V : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
  [AddCommGroup V] [Module k V] [Comodule k H V] [FiniteDimensional k V] [Nontrivial V]
  [IsSimpleOrder (Subcomodule k H V)]

/-- A connected reduced normal solvable closed subgroup acts by scalars on a simple
finite-dimensional rational representation of a reduced connected affine group. -/
theorem exists_basePointsRepresentation_eq_smul
    (I : HopfIdeal k H) (hI : I.IsNormal)
    [IsReduced (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I)]
    [ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I))]
    [Group.IsSolvable (WithConv
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I →ₐ[k] k))]
    (g : WithConv (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k H) I →ₐ[k] k)) :
    ∃ c : kˣ, Comodule.basePointsRepresentation (R := k) (H := H) V
      (AlgHom.mapDomain (CommHopfAlgCat.mkQuotient
        (_root_.CommHopfAlgCat.of k H) I).hom g) =
      (c : k) • (1 : Module.End k V) := by
  classical
  let A := _root_.CommHopfAlgCat.of k H
  let Q := CommHopfAlgCat.quotient A I
  let q := (CommHopfAlgCat.mkQuotient A I).hom
  let _ : Comodule k Q V := Comodule.Corestrict q.toCoalgHom
  obtain ⟨v, a, hv, -, hva⟩ := Comodule.hasNonzeroWeightVector_iff.mp
    (Comodule.hasNonzeroWeightVector_of_isSolvable (k := k) (H := Q) (M := V))
  obtain ⟨a, rfl⟩ := CommHopfAlgCat.mkQuotient_surjective A I a
  let N := CommHopfAlgCat.quotientPointsSubgroup A I (CommAlgCat.of k k)
  let _ : N.Normal := CommHopfAlgCat.quotientPointsSubgroup_normal A I hI _
  let ρ := Comodule.basePointsRepresentation (R := k) (H := H) V
  have heigen (n : N) : ρ n v = (n.val.ofConv a) • v := by
    obtain ⟨x, hx⟩ := n.2
    rw [← hx, CommHopfAlgCat.quotientPointsHom_apply_apply,
      CommHopfAlgCat.quotientPointsHom_apply]
    have hxv : Comodule.basePointsRepresentation (R := k) (H := Q) V x v =
        x.ofConv (q a) • v := by
      rw [Comodule.basePointsRepresentation_apply, Comodule.endOfPoint_tmul, hva]
      simp [q]
    rw [Comodule.basePointsRepresentation_corestrict q] at hxv
    exact hxv
  let χ := (ρ.comp N.subtype).unitHomOfJointEigenvector
    (fun n : N ↦ n.val.ofConv a) v hv
    (fun n ↦ Module.End.mem_eigenspace_iff.mpr (heigen n))
  have hχ (n : N) : (χ n : k) = n.val.ofConv a :=
    MonoidHom.unitHomOfJointEigenvector_apply _ _ _ _ _ n
  have hvχ : v ∈ ⨅ n : N, (ρ n).eigenspace (χ n : k) := by
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, hχ]
    exact heigen
  let ψ : NonzeroJointWeight N ρ := ⟨χ, (Submodule.ne_bot_iff _).mpr ⟨v, hvχ, hv⟩⟩
  have htop : Comodule.normalWeightSubcomodule N ψ = ⊤ :=
    (eq_bot_or_eq_top (Comodule.normalWeightSubcomodule N ψ)).resolve_left
      (Comodule.normalWeightSubcomodule_ne_bot N ψ)
  let n : N := ⟨CommHopfAlgCat.quotientPointsHom A I _ g, ⟨g, rfl⟩⟩
  refine ⟨χ n, ?_⟩
  ext w
  have hw := (Comodule.mem_normalWeightSubcomodule N ψ w).mp
    (htop ▸ Subcomodule.mem_top w) n
  exact hw

end

end TauCeti.HopfIdeal
