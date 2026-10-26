/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Space
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.Algebra.Coalgebra.Basic
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Weight decomposition of comodules over a group-like-spanned coalgebra

Let `C` be a torsion-free coalgebra over a domain `k` whose group-like elements span `C`. Over a
field and for `C` a commutative Hopf algebra, this says that `C` is the coordinate algebra of a
diagonalizable group. This file proves that every `C`-comodule is the sum of its group-like weight
spaces, and, when it is torsion-free, their internal direct sum: every representation of a
diagonalizable group is diagonalizable. Conversely, over a field, the group-like elements span
`C` as soon as every finite-dimensional subcomodule of the regular comodule is spanned by its
group-like weight spaces.

The proof expands the coaction in the basis `Subcoalgebra.groupLikeBasis` of `C` formed by the
group-like elements. Writing `ρ m = ∑_g m_g ⊗ g`, the counit law gives `m = ∑_g m_g`, and
coassociativity, read off by the coordinate functionals of the basis, shows that each `m_g` has
weight `g`.

## Main declarations

* `TauCeti.Comodule.iSup_groupLikeWeightSpace_eq_top`: a comodule over a group-like-spanned
  coalgebra is spanned by its group-like weight spaces.
* `TauCeti.Comodule.isInternal_groupLikeWeightSpace`: a torsion-free comodule over a
  group-like-spanned coalgebra is the internal direct sum of its group-like weight spaces.
* `TauCeti.Subcoalgebra.groupLikeSetSpan_eq_top_of_forall_finite_subcomodule`: conversely, a
  coalgebra over a field is spanned by its group-like elements once every finite-dimensional
  subcomodule of the regular comodule is spanned by its group-like weight spaces.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.12.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Theorem 2.2.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable {k : Type u} {C : Type v} {M : Type w}
variable [CommRing k] [IsDomain k] [AddCommGroup C] [Module k C] [Module.IsTorsionFree k C]
variable [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

/-- Comultiplying and then pairing with a functional and a group-like coordinate is the same as
scaling that coordinate by the value of the functional at the group-like element. -/
private theorem coord_comp_tensorComponent_comp_comul
    (hC : Subcoalgebra.groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤)
    (φ : Module.Dual k C) (g : GroupLike k C) :
    φ ∘ₗ _root_.LinearMap.tensorComponent ((Subcoalgebra.groupLikeBasis hC).coord g) ∘ₗ
        Coalgebra.comul =
      φ g.val • (Subcoalgebra.groupLikeBasis hC).coord g := by
  classical
  refine (Subcoalgebra.groupLikeBasis hC).ext fun h ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Subcoalgebra.groupLikeBasis_apply,
    h.isGroupLikeElem_val.comul_eq_tmul_self,
    _root_.LinearMap.tensorComponent_tmul, map_smul, LinearMap.smul_apply,
    ← Subcoalgebra.groupLikeBasis_apply hC h,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  split_ifs with hhg
  · simp [hhg, Subcoalgebra.groupLikeBasis_apply, smul_eq_mul]
  · simp

/-- The coordinate of a coaction along a group-like basis vector has that group-like weight. -/
theorem coactComponent_groupLikeBasis_coord_mem_weightSpace
    (hC : Subcoalgebra.groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤)
    (g : GroupLike k C) (m : M) :
    coactComponent (R := k) (C := C) (M := M) ((Subcoalgebra.groupLikeBasis hC).coord g) m ∈
      _root_.GroupLike.weightSpace (M := M) g := by
  let _ : Module.Projective k C := Module.Projective.of_basis (Subcoalgebra.groupLikeBasis hC)
  rw [mem_groupLikeWeightSpace_iff_forall_coactComponent_eq_smul]
  intro φ
  rw [coactComponent_coactComponent, coord_comp_tensorComponent_comp_comul,
    coactComponent_apply, map_smul, LinearMap.smul_apply, ← coactComponent_apply]

/-- **A comodule over a coalgebra spanned by its group-like elements is spanned by its group-like
weight spaces.** -/
theorem iSup_groupLikeWeightSpace_eq_top
    (hC : Subcoalgebra.groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤) :
    ⨆ g : GroupLike k C, _root_.GroupLike.weightSpace (M := M) g = ⊤ := by
  classical
  let b := Subcoalgebra.groupLikeBasis hC
  let e := TensorProduct.equivFinsuppOfBasisRight (M := M) b
  refine eq_top_iff.mpr fun m _ ↦ ?_
  have he (t : M ⊗[k] C) (g : GroupLike k C) :
      e t g = _root_.LinearMap.tensorComponent (R := k) (M := M) (b.coord g) t := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, map_add]
    | tmul x c =>
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        _root_.LinearMap.tensorComponent_tmul, Module.Basis.coord_apply]
  have hsum : coact (R := k) (C := C) m = (e (coact m)).sum fun g x ↦ x ⊗ₜ[k] g.val := by
    conv_lhs => rw [← e.symm_apply_apply (coact m)]
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply]
    simp only [b, Subcoalgebra.groupLikeBasis_apply]
  have hm : m = (e (coact m)).sum fun _ x ↦ x := by
    apply (TensorProduct.rid k M).symm.injective
    have hε := lTensor_counit_coact (R := k) (C := C) m
    rw [hsum, map_finsuppSum] at hε
    simp only [LinearMap.lTensor_tmul, GroupLike.isGroupLikeElem_val,
      IsGroupLikeElem.counit_eq_one] at hε
    rw [TensorProduct.rid_symm_apply, ← hε, TensorProduct.rid_symm_apply, Finsupp.sum,
      Finsupp.sum, TensorProduct.sum_tmul]
  rw [hm]
  refine Submodule.finsuppSum_mem _ _ _ _ fun g _ ↦ ?_
  refine Submodule.mem_iSup_of_mem g ?_
  rw [he, ← coactComponent_apply]
  exact coactComponent_groupLikeBasis_coord_mem_weightSpace hC g m

section Internal

attribute [local instance] Classical.decEq

/-- **A torsion-free comodule over a coalgebra spanned by its group-like elements is the internal
direct sum of its group-like weight spaces.** Over a field this says that every representation
of a diagonalizable group is diagonalizable. -/
theorem isInternal_groupLikeWeightSpace [Module.IsTorsionFree k M]
    (hC : Subcoalgebra.groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤) :
    DirectSum.IsInternal
      (_root_.GroupLike.weightSpace (M := M) : GroupLike k C → Submodule k M) := by
  classical
  let _ : Module.Projective k C := Module.Projective.of_basis (Subcoalgebra.groupLikeBasis hC)
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨iSupIndep_groupLikeWeightSpace, iSup_groupLikeWeightSpace_eq_top hC⟩

end Internal

end TauCeti.Comodule

namespace TauCeti.Subcoalgebra

universe u v

variable {k : Type u} {C : Type v} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- **A coalgebra over a field is spanned by its group-like elements once every
finite-dimensional subcomodule of the regular comodule is spanned by its group-like weight
spaces.** A weight vector of the regular comodule is a scalar multiple of its weight, and every
element lies in a finite-dimensional subcomodule. This is the converse of
`TauCeti.Comodule.iSup_groupLikeWeightSpace_eq_top`. -/
theorem groupLikeSetSpan_eq_top_of_forall_finite_subcomodule
    (h : ∀ N : Subcomodule k C C, Module.Finite k N.toSubmodule →
      ⨆ g : GroupLike k C, _root_.GroupLike.weightSpace (M := N) g = ⊤) :
    groupLikeSetSpan (R := k) (C := C) Set.univ = ⊤ := by
  rw [groupLikeSetSpan_eq_top_iff_span_eq_top]
  refine eq_top_iff.mpr fun c _ ↦ ?_
  obtain ⟨N, hNfin, hN⟩ := Subcomodule.exists_finite_subcomodule_mem (R := k) (C := C) c
  -- A weight vector in the regular representation is a counit multiple of its character.
  have hle : (⨆ g : GroupLike k C, _root_.GroupLike.weightSpace (M := N) g) ≤
      (Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := C)))).comap
        (N.subtype.toLinearMap) := by
    refine iSup_le fun g n hn ↦ ?_
    have hw := N.subtype.map_mem_groupLikeWeightSpace hn
    rw [_root_.GroupLike.mem_weightSpace, Comodule.instSelf_coact] at hw
    have hmem : N.subtype n ∈
        Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := C))) := by
      rw [Coalgebra.eq_counit_smul_of_comul_eq_tmul hw]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self g))
    simpa only [Submodule.mem_comap, Comodule.Hom.coe_toLinearMap] using hmem
  have hmem := hle (h N hNfin ▸ (Submodule.mem_top : (⟨c, hN⟩ : N) ∈ ⊤))
  simpa only [Submodule.mem_comap, Subcomodule.subtype_toLinearMap,
    SMulMemClass.subtype_apply] using hmem

end TauCeti.Subcoalgebra
