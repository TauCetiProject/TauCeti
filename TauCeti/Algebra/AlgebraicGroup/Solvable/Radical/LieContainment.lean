/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Construction
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Lie
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Lie
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Quotient
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Normal subgroups with solvable Lie algebra

Over an algebraically closed field of characteristic zero, the identity component of a
normal closed subgroup with solvable Lie algebra lies in the solvable radical. Consequently
the subgroup's entire tangent Lie algebra lies in the tangent Lie algebra of the radical.
The subgroup itself can be disconnected, and need not lie in the radical.

For a connected ambient group, the Lie algebra of its solvable radical is exactly the
radical of its Lie algebra. This comparison links group-theoretic semisimplicity with
Lie-algebra semisimplicity and Cartan's criterion.

This is the passage from a normal subgroup realizing a solvable Lie ideal to containment
of that ideal in `Lie(R(G))`. It uses the solvable-Lie-algebra criterion from `Solvable.Lie`,
the invariance of the Lie algebra under passage to the identity component, and the universal
property of the group radical. Smoothness follows from Cartier's theorem.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 22.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- The identity component of a normal closed subgroup with solvable Lie algebra is a
connected normal smooth solvable closed subgroup in characteristic zero. -/
theorem IsNormal.isSolvableRadicalCandidate_identityComponent (hI : I.IsNormal)
    [LieAlgebra.IsSolvable (I.lieSubalgebra (B := k))] :
    IsSolvableRadicalCandidate H I.identityComponent := by
  let _ : IsReduced H := HopfAlgebra.isReduced_of_charZero k H
  let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H I) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_charZero k _)
  let _ : IsReduced (FiniteTypeCommHopfAlgCat.quotient H I) :=
    HopfAlgebra.isReduced_of_charZero k _
  let Q := FiniteTypeCommHopfAlgCat.quotient H I.identityComponent
  have hconn := I.geometricallyConnected_identityComponent
  let _ : LieAlgebra.IsSolvable (I.identityComponent.lieSubalgebra (B := k)) := by
    rw [lieSubalgebra_identityComponent]
    infer_instance
  let _ : LieAlgebra.IsSolvable (Derivation k Q (Bialgebra.CounitAlgebra k Q k)) :=
    (LieAlgebra.solvable_iff_equiv_solvable (I.identityComponent.quotientLieEquiv (B := k))).mpr
      inferInstance
  exact .mk hI.identityComponent hconn I.smooth_identityComponent
    (geometricallySolvablePointsCommHopfAlgProperty.of_geometricallyConnected_of_isSolvable_lie
      hconn)

/-- The tangent Lie algebra of a normal closed subgroup with solvable Lie algebra lies in
the tangent Lie algebra of the solvable radical, even if that subgroup is disconnected. -/
theorem IsNormal.lieSubalgebra_le_solvableRadical (hI : I.IsNormal)
    [LieAlgebra.IsSolvable (I.lieSubalgebra (B := k))] :
    I.lieSubalgebra (B := k) ≤
      (FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal H).lieSubalgebra (B := k) := by
  have hle := FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_le H _
    hI.isSolvableRadicalCandidate_identityComponent
  rw [← I.lieSubalgebra_identityComponent]
  intro d hd
  rw [mem_lieSubalgebra_iff] at hd ⊢
  exact fun x hx ↦ hd x (hle hx)

end TauCeti.HopfIdeal

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

/-- For a connected affine group over an algebraically closed field of characteristic zero,
the Lie algebra of its solvable radical equals the solvable radical of its Lie algebra. -/
theorem lieIdeal_solvableRadicalDefiningIdeal_eq_radical
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [ConnectedSpace (PrimeSpectrum H)] :
    (isNormal_solvableRadicalDefiningIdeal H).lieIdeal (B := k) =
      LieAlgebra.radical k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let L := Module.Dual k (Bialgebra.CotangentSpace k H)
  let e : L ≃ₗ⁅k⁆ Derivation k H (Bialgebra.CounitAlgebra k H k) :=
    Derivation.cotangentDualLieEquiv
  obtain ⟨I, hI, hLie⟩ := exists_isNormal_lieSubalgebra_eq_radical H
  have hLie' : I.lieSubalgebra (B := k) =
      (LieAlgebra.radical k L).toLieSubalgebra.comap e.symm.toLieHom := hLie
  have hmap : (I.lieSubalgebra (B := k)).map e.symm.toLieHom =
      (LieAlgebra.radical k L).toLieSubalgebra := by
    ext x
    simp only [LieSubalgebra.mem_map, hLie', LieSubalgebra.mem_comap,
      LieEquiv.coe_toLieHom]
    exact ⟨fun ⟨d, hd, hdx⟩ ↦ hdx ▸ hd,
      fun hx ↦ ⟨e x, by simpa only [LieEquiv.symm_apply_apply] using hx,
        e.symm_apply_apply x⟩⟩
  have : LieAlgebra.IsSolvable (LieAlgebra.radical k L).toLieSubalgebra := by
    exact LieAlgebra.radicalIsSolvable k L
  let _ : LieAlgebra.IsSolvable (I.lieSubalgebra (B := k)) :=
    (LieAlgebra.solvable_iff_equiv_solvable
      (e.symm.ofSubalgebras _ _ hmap)).mpr inferInstance
  have hle := hI.lieSubalgebra_le_solvableRadical
  refine le_antisymm
    (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H).lieIdeal_le_radical ?_
  have hker : LieAlgebra.IsSolvable e.toLieHom.ker := by
    rw [(LieHom.ker_eq_bot e.toLieHom).mpr e.injective]
    infer_instance
  rw [← LieIdeal.radical_map_eq e.toLieHom e.surjective hker,
    LieIdeal.map_le_iff_le_comap]
  intro x hx
  rw [LieIdeal.mem_comap, ← LieIdeal.mem_toLieSubalgebra,
    HopfIdeal.IsNormal.lieIdeal_toLieSubalgebra]
  apply hle
  rw [hLie', LieSubalgebra.mem_comap]
  simpa only [LieEquiv.coe_toLieHom, LieEquiv.symm_apply_apply,
    LieIdeal.mem_toLieSubalgebra] using hx

end TauCeti.FiniteTypeCommHopfAlgCat
