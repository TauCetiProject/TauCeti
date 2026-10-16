/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Trigonalizable
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.Coalgebra.Comodule.Weight.Decomposition
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic

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

Reducedness cannot be dropped: in characteristic `p`, the group `αₚ` has only the identity point,
which is semisimple, but it is not diagonalizable.

## Main declarations

* `TauCeti.Comodule.iSup_groupLikeWeightSpace_eq_top_of_isSemisimple`: a finite-dimensional
  representation on which the points act by commuting semisimple operators is spanned by its
  weight spaces.
* `TauCeti.Comodule.isSemisimple_basePointsRepresentation`: a semisimple point acts semisimply on
  every finite-dimensional representation.
* `TauCeti.HopfAlgebra.groupLikeSetSpan_eq_top_of_isSemisimplePoint`: a reduced commutative
  affine group whose points are semisimple is diagonalizable.
* `TauCeti.torusCommHopfAlgProperty_of_isSemisimplePoint`: if it is moreover connected, it is a
  torus.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.
* T. A. Springer, *Linear Algebraic Groups*, §§2.4 and 3.2.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti

universe u v w

namespace Comodule

section WeightSpaces

variable {k : Type u} {H : Type v} {M : Type w}
variable [Field k] [CommRing H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M]
variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]

/-- If the base-valued points of a reduced finite-type Hopf algebra over an algebraically closed
field act on a finite-dimensional comodule by pairwise-commuting semisimple operators, then the
comodule is spanned by its group-like weight spaces. -/
theorem iSup_groupLikeWeightSpace_eq_top_of_isSemisimple [FiniteDimensional k M]
    (hcomm : Pairwise fun g h : WithConv (H →ₐ[k] k) ↦
      Commute (basePointsRepresentation (R := k) (H := H) M g)
        (basePointsRepresentation (R := k) (H := H) M h))
    (hss : ∀ g : WithConv (H →ₐ[k] k),
      (basePointsRepresentation (R := k) (H := H) M g).IsSemisimple) :
    ⨆ c : GroupLike k H, _root_.GroupLike.weightSpace (M := M) c = ⊤ := by
  rw [eq_top_iff, ← iSup_iInf_eigenspace_eq_top_of_isSemisimple
    (fun g ↦ basePointsRepresentation (R := k) (H := H) M g) hcomm hss]
  refine iSup_le fun χ v hv ↦ ?_
  rcases eq_or_ne v 0 with rfl | hv0
  · exact zero_mem _
  obtain ⟨c, hc⟩ := exists_mem_groupLikeWeightSpace_of_basePointsRepresentation_stable
    (k ∙ v) v hv0 rfl fun g m hm ↦ by
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hm
      rw [map_smul, Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hv g),
        smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  exact Submodule.mem_iSup_of_mem c hc

end WeightSpaces

variable {k : Type u} {H : Type v} {M : Type u}
variable [Field k] [CommRing H] [HopfAlgebra k H]
variable [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- A semisimple base-valued point acts by a semisimple operator on every finite-dimensional
comodule. -/
theorem isSemisimple_basePointsRepresentation {g : WithConv (H →ₐ[k] k)}
    (hg : HopfAlgebra.IsSemisimplePoint g) :
    (basePointsRepresentation (R := k) (H := H) M g).IsSemisimple := by
  refine (LinearEquiv.isSemisimple_iff (f := endOfPoint M g.ofConv) _ (TensorProduct.lid k M)
    ?_).mp ((HopfAlgebra.isSemisimplePoint_iff_forall_isSemisimple_endOfPoint g).mp hg
      (FGComoduleCat.of (R := k) (C := H) M))
  refine TensorProduct.ext' fun a m ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, endOfPoint_tmul,
    endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
  simp

end Comodule

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
    fun g ↦ Comodule.isSemisimple_basePointsRepresentation (hss g)

end HopfAlgebra

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

end TauCeti
