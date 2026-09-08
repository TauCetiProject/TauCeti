/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.StandardComodule
import TauCeti.Algebra.AlgebraicGroup.Symplectic.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Connected
import TauCeti.Algebra.AlgebraicGroup.Symplectic.Smooth
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Faithful
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The symplectic group is reductive

The coordinate Hopf algebra of the standard symplectic group `Sp₂ₘ` is reductive over every
field, in every natural rank and in arbitrary characteristic.

The coordinate algebra is smooth and geometrically connected. To eliminate a normal smooth
unipotent closed subgroup over an algebraically closed field, use the standard representation.
It is simple in positive rank, hence completely reducible, while in rank zero its carrier is a
singleton. Normal unipotent subgroups therefore act trivially on it. Since the standard
representation is faithful in every rank, the subgroup is the identity subgroup.

The result over an arbitrary field follows by transporting this argument across the canonical
base-change identification

`AlgebraicClosure k ⊗[k] O(Sp₂ₘ) ≃ O(Sp₂ₘ, AlgebraicClosure k)`.

## Main declarations

* `TauCeti.Symplectic.eq_augmentation_of_isNormal_of_smoothUnipotent`: a normal smooth
  unipotent closed subgroup of `Sp₂ₘ` over an algebraically closed field is trivial.
* `TauCeti.Symplectic.reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra`:
  `Sp₂ₘ` is reductive over every field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§19.b and 24.6.
* T. A. Springer, *Linear Algebraic Groups*, §§2.2, 2.4, and Chapter 8.
* The ReductiveGroups roadmap, Layer 6 and its `Sp₂ₙ` worked example, which requests this
  geometric `R_u = 1` proof in arbitrary characteristic.
-/

public section

open CategoryTheory

namespace TauCeti.Symplectic

universe u

noncomputable section

open HopfIdeal

/-- The coordinate Hopf algebra and the underlying object of its finite-type package are
canonically identical. -/
private noncomputable def coordinateHopfAlgebraFiniteTypeObjIso
    (R : Type u) [CommRing R] (m : Nat) :
    coordinateHopfAlgebra R m ≅ (finiteTypeCoordinateHopfAlgebra R m).obj :=
  eqToIso (finiteTypeCoordinateHopfAlgebra_obj R m).symm

/-- A normal smooth unipotent closed subgroup of `Sp₂ₘ` over an algebraically closed field is
trivial. No positivity hypothesis on `m` is needed. -/
theorem eq_augmentation_of_isNormal_of_smoothUnipotent
    (k : Type u) [Field k] [IsAlgClosed k] (m : Nat)
    (I : HopfIdeal k (finiteTypeCoordinateHopfAlgebra k m)) (hI : I.IsNormal)
    (hU : smoothUnipotentCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.quotient (finiteTypeCoordinateHopfAlgebra k m) I)) :
    I = HopfIdeal.augmentation k (finiteTypeCoordinateHopfAlgebra k m) := by
  let e := coordinateHopfAlgebraFiniteTypeObjIso k m
  let H : FiniteTypeCommHopfAlgCat k :=
    ⟨coordinateHopfAlgebra k m, by
      rw [← finiteTypeCoordinateHopfAlgebra_obj]
      exact (finiteTypeCoordinateHopfAlgebra k m).property⟩
  let _ : IsReduced H := by
    -- `H` packages this coordinate algebra with its finite-type proof, so its carrier is
    -- definitionally the coordinate algebra on which smoothness supplies reducedness.
    change IsReduced (coordinateHopfAlgebra k m)
    exact isReduced_of_smooth_of_field k _
  let _ : Comodule k (coordinateHopfAlgebra k m) (Fin (m + m) → k) := standardComodule k m
  have hcr : Comodule.IsCompletelyReducible k (coordinateHopfAlgebra k m)
      (Fin (m + m) → k) := by
    cases m with
    | zero =>
        let _ : Subsingleton (Fin (0 + 0) → k) :=
          ⟨fun f g => funext fun i => Fin.elim0 i⟩
        exact Comodule.isCompletelyReducible_of_subsingleton
    | succ m =>
        let _ : NeZero m.succ := ⟨Nat.succ_ne_zero m⟩
        exact Comodule.isCompletelyReducible_of_isSimpleOrder
  exact HopfIdeal.eq_augmentation_of_isNormal_of_smoothUnipotent_of_isFaithful_of_iso
    k H (Fin (m + m) → k) (finiteTypeCoordinateHopfAlgebra k m) e hcr
      (isFaithful_standardComodule k m) I hI hU

/-- **The standard symplectic group is reductive over every field.** -/
theorem reductiveCommHopfAlgProperty_finiteTypeCoordinateHopfAlgebra
    (k : Type u) [Field k] (m : Nat) :
    reductiveCommHopfAlgProperty k (finiteTypeCoordinateHopfAlgebra k m) := by
  let e := coordinateHopfAlgebraFiniteTypeObjIso k m
  apply reductiveCommHopfAlgProperty_of_geometricFiber_iso k _
    (finiteTypeCoordinateHopfAlgebra (AlgebraicClosure k) m)
    ((smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso e
        ((smoothCommHopfAlgProperty_iff _).mpr inferInstance))
    ((geometricallyConnectedCommHopfAlgProperty k).prop_of_iso e
      (geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra k m))
    (finiteTypeCoordinateHopfAlgebraBaseChangeIso k (AlgebraicClosure k) m)
  intro I hI hU
  exact eq_augmentation_of_isNormal_of_smoothUnipotent
    (AlgebraicClosure k) m I hI hU

end

end TauCeti.Symplectic
