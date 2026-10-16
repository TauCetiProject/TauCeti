/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Representation.Diagonalization
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Span
import TauCeti.Algebra.Coalgebra.Cocommutative

/-!
# Recognizing diagonalizable groups from semisimple points

A reduced commutative affine group of finite type over an algebraically closed field is
diagonalizable if all its rational points are semisimple. Commuting semisimple operators
simultaneously diagonalize every finite-dimensional representation, and point separation
makes their eigenvectors algebraic weight vectors. Applying this to the regular comodule
shows that group-like elements span the coordinate Hopf algebra.

Reducedness cannot be dropped: infinitesimal groups such as `αₚ` have only the identity
geometric point but need not be diagonalizable. Connectedness is not required, so the
recognition theorem also applies to smooth finite diagonalizable groups.

The proof combines the simultaneous diagonalization API with the reconstruction theorem
`TauCeti.DiagonalizableGroup.essImage_coordinateRingFunctor`.

## References

* T. A. Springer, *Linear Algebraic Groups*, §3.2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (H : FiniteTypeCommHopfAlgCat.{u, u} k) [IsReduced H]

namespace DiagonalizableGroup

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
      (isSemisimplePoint (AlgHom.mapDomain e'.toBialgHom g))
  · rintro ⟨hc, hss⟩
    let _ := hc
    rw [groupLikeSpannedProperty_iff]
    apply Subcoalgebra.groupLikeSetSpan_eq_top_of_forall_iSup_groupLikeWeightSpace_eq_top
    intro M
    apply Comodule.iSup_groupLikeWeightSpace_eq_top_of_commute_of_isSemisimple
    · exact fun g h _ ↦ (Commute.all g h).map (Comodule.basePointsRepresentation M)
    · intro g
      exact (HopfAlgebra.isSemisimplePoint_iff_forall_isSemisimple_basePointsRepresentation g).mp
        (hss g) M

end DiagonalizableGroup

end TauCeti
