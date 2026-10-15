/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.GroupLike.Kernel
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.CharacterLattice.Functoriality
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Kernels of homomorphisms of multiplicative-type groups

For a homomorphism of groups of multiplicative type over a field, the geometric kernel
has coordinate algebra the group algebra of the geometric character cokernel. In particular,
the kernel over the original field is finite exactly when this cokernel is finite, and
the `Module.finrank` of its coordinate algebra equals the `Nat.card` of the cokernel.
For a finite kernel, this is its dimension equal to the cokernel's cardinality; in the
infinite case both quantities are zero. These statements apply to arbitrary homomorphisms,
without an isogeny or smoothness hypothesis.

The Hopf-algebra comparison retains the scheme structure of the kernel. Thus a finite kernel's rank
counts infinitesimal structure as well as geometric points; for example, it gives rank `p`
for the kernel `μ_p` of the `p`th power map in characteristic `p`.

The intrinsic diagonalizable-kernel calculation and the quotient base-change comparison
supply the geometric identification; faithful-flat descent transfers finiteness to the
original field.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9(b) and §12.d.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.multiplicativeTypeCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
variable (hH : multiplicativeTypeCommHopfAlgProperty k H)
variable (hK : multiplicativeTypeCommHopfAlgProperty k K) (f : H.obj ⟶ K.obj)

/-- The geometric kernel comparison with an explicitly identified character map. -/
private noncomputable def geometricKernelCoordinateIsoAux
    (p : CommHopfAlgCat.geometricCharacterGroup H.obj →*
      CommHopfAlgCat.geometricCharacterGroup K.obj)
    (hp : p = TauCeti.GroupLike.map
      (CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) f).hom) :
    CommHopfAlgCat.baseChange (K := AlgebraicClosure k)
        (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) ≅
      CommHopfAlgCat.of (AlgebraicClosure k)
        (MonoidAlgebra (AlgebraicClosure k)
          (CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
            p.range)) := by
  subst p
  exact
    (CommHopfAlgCat.quotientBaseChangeIso (K := AlgebraicClosure k)
        (CommHopfAlgCat.kernelHopfIdeal f)).symm ≪≫
      eqToIso (congrArg (CommHopfAlgCat.quotient _)
        (CommHopfAlgCat.baseChangeHopfIdeal_kernelHopfIdeal f)) ≪≫
      DiagonalizableGroup.kernelGroupLikeCoordinateIso
        ((Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top).mp
          ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
            ((multiplicativeTypeCommHopfAlgProperty_iff k H).mp hH)))
        ((Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top).mp
          ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
            ((multiplicativeTypeCommHopfAlgProperty_iff k K).mp hK)))
        (CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) f)

private theorem geometricKernelCoordinateIsoAux_comp
    (p : CommHopfAlgCat.geometricCharacterGroup H.obj →*
      CommHopfAlgCat.geometricCharacterGroup K.obj)
    (hp : p = TauCeti.GroupLike.map
      (CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k) f).hom) :
    CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k)
        (CommHopfAlgCat.mkQuotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) ≫
        (geometricKernelCoordinateIsoAux hH hK f p hp).hom =
      (CommHopfAlgCat.evaluationIso
        ((Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top).mp
          ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
            ((multiplicativeTypeCommHopfAlgProperty_iff k K).mp hK)))).inv ≫
        CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom (AlgebraicClosure k)
          (QuotientGroup.mk' p.range)) := by
  subst p
  simp only [geometricKernelCoordinateIsoAux, Iso.trans_hom, Iso.symm_hom, eqToIso.hom]
  rw [← CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom (K := AlgebraicClosure k)]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, CommHopfAlgCat.mkQuotient_comp_eqToHom
    (CommHopfAlgCat.baseChangeHopfIdeal_kernelHopfIdeal f).symm]
  exact DiagonalizableGroup.mkQuotient_comp_kernelGroupLikeCoordinateIso_hom _ _ _

/-- The geometric kernel of a homomorphism of multiplicative-type groups has coordinate
Hopf algebra the group algebra of its geometric character cokernel. -/
noncomputable def geometricKernelCoordinateIso :
    CommHopfAlgCat.baseChange (K := AlgebraicClosure k)
        (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) ≅
      CommHopfAlgCat.of (AlgebraicClosure k)
        (MonoidAlgebra (AlgebraicClosure k)
          (CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
            (CommHopfAlgCat.geometricCharacterMap f).range)) :=
  geometricKernelCoordinateIsoAux hH hK f (CommHopfAlgCat.geometricCharacterMap f)
    (CommHopfAlgCat.geometricCharacterMap_eq_groupLikeMap f)

/-- The geometric kernel comparison commutes with the scalar-extended quotient map.
The right side expresses the ambient algebra in intrinsic character coordinates and
then applies the character quotient. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_mkQuotient_comp_geometricKernelCoordinateIso_hom :
    CommHopfAlgCat.baseChangeMap (K := AlgebraicClosure k)
        (CommHopfAlgCat.mkQuotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) ≫
        (geometricKernelCoordinateIso hH hK f).hom =
      (CommHopfAlgCat.evaluationIso
        ((Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top).mp
          ((DiagonalizableGroup.groupLikeSpannedProperty_iff _ _).mp
            ((multiplicativeTypeCommHopfAlgProperty_iff k K).mp hK)))).inv ≫
        CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom (AlgebraicClosure k)
          (QuotientGroup.mk' (CommHopfAlgCat.geometricCharacterMap f).range)) :=
  geometricKernelCoordinateIsoAux_comp hH hK f (CommHopfAlgCat.geometricCharacterMap f)
    (CommHopfAlgCat.geometricCharacterMap_eq_groupLikeMap f)

include hH hK in
/-- A homomorphism of multiplicative-type groups has finite scheme-theoretic kernel
exactly when its geometric character map has finite cokernel. -/
theorem moduleFinite_kernelCoordinate_iff_finite_quotient :
    Module.Finite k (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) ↔
      Finite (CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
        (CommHopfAlgCat.geometricCharacterMap f).range) := by
  let L := AlgebraicClosure k
  let Q := CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)
  let C := CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
    (CommHopfAlgCat.geometricCharacterMap f).range
  let e : L ⊗[k] Q ≃ₗ[L] (C →₀ L) :=
    (CommHopfAlgCat.ofIso (geometricKernelCoordinateIso hH hK f)).toAlgEquiv.toLinearEquiv ≪≫ₗ
      MonoidAlgebra.coeffLinearEquiv L (S := L) (M := C)
  have hfinite : Module.Finite L (L ⊗[k] Q) ↔ Finite C := by
    rw [Module.Finite.equiv_iff e]
    simp [Module.finite_finsupp_self_iff, not_subsingleton L]
  constructor
  · intro hQ
    let _ := hQ
    exact hfinite.mp inferInstance
  · intro hC
    let _ := hfinite.mpr hC
    exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L

include hH hK in
/-- The `Module.finrank` of a multiplicative-type kernel's coordinate algebra over the
ground field equals the `Nat.card` of the geometric character cokernel. For a finite
kernel, this is its dimension, or scheme-theoretic rank, even when the kernel is
nonreduced; in the infinite case both quantities are zero. -/
theorem finrank_kernelCoordinate :
    Module.finrank k (CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f)) =
      Nat.card (CommHopfAlgCat.geometricCharacterGroup K.obj ⧸
        (CommHopfAlgCat.geometricCharacterMap f).range) := by
  let e := (CommHopfAlgCat.ofIso (geometricKernelCoordinateIso hH hK f)).toAlgEquiv.toLinearEquiv
  rw [← Module.finrank_baseChange (R := AlgebraicClosure k), e.finrank_eq]
  exact Module.finrank_eq_nat_card_basis (MonoidAlgebra.basis _ (AlgebraicClosure k))

end TauCeti.multiplicativeTypeCommHopfAlgProperty
