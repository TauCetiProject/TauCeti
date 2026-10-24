/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.Coalgebra.Cocommutative
import TauCeti.Algebra.Coalgebra.Comodule.Weight.Decomposition

/-!
# Commutative groups of semisimple elements are diagonalizable

Let `H` be the coordinate Hopf algebra of a reduced commutative affine group of finite type over
an algebraically closed field `k`. If every `k`-point of the group is semisimple, then the group
is diagonalizable: the group-like elements span `H`. If the group is moreover connected, it is a
torus.

On a finite-dimensional representation the points act by pairwise-commuting semisimple
operators, so the representation is the sum of the joint eigenspaces of these operators. Each
nonzero joint eigenvector spans a line stable under every point, and point separation on the
reduced coordinate ring makes that line a subcomodule; hence the vector is a weight vector.
Applying this to the finite-dimensional subcomodules of the regular representation shows that
group-like elements span `H`.

Conversely, every point of a diagonalizable group is semisimple, and its coordinate Hopf algebra
is cocommutative. Combined with the reconstruction theorem
`TauCeti.DiagonalizableGroup.essImage_coordinateRingFunctor`, this characterizes diagonalizable
groups among reduced affine groups of finite type. Connectedness is not required for this
characterization, so it also applies to smooth finite diagonalizable groups.

Reducedness cannot be dropped: in characteristic `p`, the group `αₚ` has only the identity point,
which is semisimple, but it is not diagonalizable.

## Main declarations

* `TauCeti.HopfAlgebra.groupLikeSetSpan_eq_top_of_isSemisimplePoint`: a reduced commutative
  affine group whose points are semisimple is diagonalizable.
* `TauCeti.torusCommHopfAlgProperty_of_isSemisimplePoint`: if it is moreover connected, it is a
  torus.
* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty_iff_isCocomm_and_forall_isSemisimplePoint`:
  a reduced affine group is diagonalizable exactly when it is commutative and its points are
  semisimple.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.
* T. A. Springer, *Linear Algebraic Groups*, §§2.4 and 3.2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti

universe u

namespace HopfAlgebra

variable (k : Type u) (H : Type u) [Field k] [CommRing H] [HopfAlgebra k H]
variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H] [Coalgebra.IsCocomm k H]

/-- **A reduced commutative affine group whose points are all semisimple is diagonalizable.**
Over an algebraically closed field, the coordinate Hopf algebra of such a group of finite type is
spanned by its group-like elements. -/
theorem groupLikeSetSpan_eq_top_of_isSemisimplePoint
    (hss : ∀ g : WithConv (H →ₐ[k] k), IsSemisimplePoint g) :
    Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ = ⊤ := by
  refine Subcoalgebra.groupLikeSetSpan_eq_top_of_forall_finite_subcomodule fun N hNfin ↦ ?_
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  -- A subcomodule and its underlying submodule subtype the same carrier.
  have _ : Module.Finite k N := hNfin
  exact Comodule.iSup_groupLikeWeightSpace_eq_top_of_isSemisimple
    (fun g h _ ↦ (Commute.all g h).map (Comodule.basePointsRepresentation (R := k) (H := H) N))
    fun g ↦ (hss g).isSemisimple_basePointsRepresentation

end HopfAlgebra

section

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k)
variable [IsReduced H] [Coalgebra.IsCocomm k H] [ConnectedSpace (PrimeSpectrum H)]

/-- **A reduced connected commutative affine group whose points are all semisimple is a torus.**
This holds over an algebraically closed field, for a group of finite type. -/
theorem torusCommHopfAlgProperty_of_isSemisimplePoint
    (hss : ∀ g : WithConv (H →ₐ[k] k), HopfAlgebra.IsSemisimplePoint g) :
    torusCommHopfAlgProperty k H :=
  torusCommHopfAlgProperty.of_groupLikeSetSpan_eq_top H
    (HopfAlgebra.groupLikeSetSpan_eq_top_of_isSemisimplePoint k H hss)

end

namespace DiagonalizableGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H]

/-- Over an algebraically closed field, a reduced affine group of finite type is
diagonalizable exactly when it is commutative and every rational point is semisimple. -/
theorem groupLikeSpannedProperty_iff_isCocomm_and_forall_isSemisimplePoint :
    groupLikeSpannedProperty k H ↔
      Coalgebra.IsCocomm k H ∧
        ∀ g : WithConv (H →ₐ[k] k), HopfAlgebra.IsSemisimplePoint g := by
  constructor
  · intro hH
    rw [← essImage_coordinateRingFunctor] at hH
    obtain ⟨G, ⟨e⟩⟩ := hH
    have e₀ : (coordinateRing k G).obj ≅ H.obj := by
      simpa only [coordinateRingFunctor_obj, ObjectProperty.ι_obj] using
        ((finiteTypeCommHopfAlgProperty k).ι.mapIso e)
    let e' : MonoidAlgebra k G ≃ₐc[k] H := _root_.CommHopfAlgCat.ofIso e₀
    have hc : Coalgebra.IsCocomm k H :=
      e'.toCoalgEquiv.toCoalgHom.isCocomm_of_surjective e'.surjective
    refine ⟨hc, fun g ↦ ?_⟩
    exact (HopfAlgebra.isSemisimplePoint_mapDomain_iff e' g).mp
      (isSemisimplePoint (BialgHom.mapDomain (e' : MonoidAlgebra k G →ₐc[k] H) g))
  · rintro ⟨hc, hss⟩
    let _ := hc
    rw [groupLikeSpannedProperty_iff]
    exact HopfAlgebra.groupLikeSetSpan_eq_top_of_isSemisimplePoint k H hss

end DiagonalizableGroup

end TauCeti
