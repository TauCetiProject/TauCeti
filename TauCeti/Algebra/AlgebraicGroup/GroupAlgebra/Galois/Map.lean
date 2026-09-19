/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Splitting
public import TauCeti.Algebra.HopfAlgebra.Basic

/-!
# Morphisms of descended group algebras

An equivariant homomorphism of abelian groups with Galois action induces a homomorphism
of their invariant coordinate algebras. For a finite Galois extension this preserves the
descended Hopf structure. The construction respects identities and composition, and its
scalar extension agrees with the usual map of split group algebras under the splitting
isomorphisms. These are the coordinate morphisms needed to recover groups of multiplicative
type, and in particular tori, functorially from their character groups.

The split map is Mathlib's `MonoidAlgebra.mapDomainBialgHom`; only its descent is constructed
here. No finite-generation or torsion-freeness assumption on the exponent groups is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L M N P : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

variable [Field k] [Field L] [Algebra k L]
variable {rho : Representation ℤ (L ≃ₐ[k] L) M}
variable {tau : Representation ℤ (L ≃ₐ[k] L) N}
variable {upsilon : Representation ℤ (L ≃ₐ[k] L) P}

/-- An equivariant map of exponent groups induces a map of invariant algebras. -/
noncomputable def groupAlgebraInvariantsAlgHom (f : Representation.IntertwiningMap rho tau) :
    groupAlgebraInvariants rho →ₐ[k] groupAlgebraInvariants tau :=
  ((((MonoidAlgebra.mapDomainBialgHom L
    f.toLinearMap.toAddMonoidHom.toMultiplicative).toAlgHom).restrictScalars k).comp
      (groupAlgebraInvariants rho).val).codRestrict _ fun x ↦ by
        rw [mem_groupAlgebraInvariants_iff]
        intro sigma
        simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Subalgebra.val_apply,
          BialgHom.coe_toAlgHom] using
          (groupAlgebraAction_mapDomainBialgHom f sigma x).trans
            (congrArg (MonoidAlgebra.mapDomainBialgHom L
              f.toLinearMap.toAddMonoidHom.toMultiplicative)
                ((mem_groupAlgebraInvariants_iff rho x).mp x.property sigma))

/-- The descended algebra map is the restriction of the split group-algebra map. -/
@[simp]
theorem coe_groupAlgebraInvariantsAlgHom (f : Representation.IntertwiningMap rho tau)
    (x : groupAlgebraInvariants rho) :
    (groupAlgebraInvariantsAlgHom f x : MonoidAlgebra L (Multiplicative N)) =
      MonoidAlgebra.mapDomainBialgHom L f.toLinearMap.toAddMonoidHom.toMultiplicative
        (x : MonoidAlgebra L (Multiplicative M)) := (rfl)

/-- Descent of the identity exponent map is the identity algebra map. -/
@[simp]
theorem groupAlgebraInvariantsAlgHom_id :
    groupAlgebraInvariantsAlgHom (Representation.IntertwiningMap.id rho) =
      AlgHom.id k (groupAlgebraInvariants rho) := by
  have h : (Representation.IntertwiningMap.id rho).toLinearMap.toAddMonoidHom.toMultiplicative =
      MonoidHom.id (Multiplicative M) := by
    ext m
    simp
  apply AlgHom.ext
  intro x
  apply Subtype.val_injective
  simp only [AlgHom.id_apply, coe_groupAlgebraInvariantsAlgHom, h,
    MonoidAlgebra.mapDomainBialgHom_id, BialgHom.id_apply]

/-- Descent of exponent maps respects composition. -/
@[simp]
theorem groupAlgebraInvariantsAlgHom_comp (f : Representation.IntertwiningMap rho tau)
    (g : Representation.IntertwiningMap tau upsilon) :
    groupAlgebraInvariantsAlgHom (g.comp f) =
      (groupAlgebraInvariantsAlgHom g).comp (groupAlgebraInvariantsAlgHom f) := by
  have h : (g.comp f).toLinearMap.toAddMonoidHom.toMultiplicative =
      g.toLinearMap.toAddMonoidHom.toMultiplicative.comp
        f.toLinearMap.toAddMonoidHom.toMultiplicative := by
    ext m
    simp
  apply AlgHom.ext
  intro x
  apply Subtype.val_injective
  simp only [AlgHom.comp_apply, coe_groupAlgebraInvariantsAlgHom, h,
    MonoidAlgebra.mapDomainBialgHom_comp, BialgHom.comp_apply]

variable [FiniteDimensional k L] [IsGalois k L]

private theorem invariantsMap_counit (f : Representation.IntertwiningMap rho tau) :
    (Bialgebra.counitAlgHom k (groupAlgebraInvariants tau)).comp
        (groupAlgebraInvariantsAlgHom f) =
      Bialgebra.counitAlgHom k (groupAlgebraInvariants rho) := by
  ext x
  apply (FaithfulSMul.algebraMap_injective k L)
  simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply,
    counit_groupAlgebraInvariants, algebraMap_groupAlgebraInvariantsCounit,
    coe_groupAlgebraInvariantsAlgHom]
  exact CoalgHomClass.counit_comp_apply _ _

private theorem invariantsMap_tensor (f : Representation.IntertwiningMap rho tau)
    (t : groupAlgebraInvariants rho ⊗[k] groupAlgebraInvariants rho) :
    (groupAlgebraInvariantsTensorEquiv tau
        (Algebra.TensorProduct.map (groupAlgebraInvariantsAlgHom f)
          (groupAlgebraInvariantsAlgHom f) t) :
      MonoidAlgebra L (Multiplicative N) ⊗[L] MonoidAlgebra L (Multiplicative N)) =
    Algebra.TensorProduct.map
        (MonoidAlgebra.mapDomainBialgHom L f.toLinearMap.toAddMonoidHom.toMultiplicative).toAlgHom
        (MonoidAlgebra.mapDomainBialgHom L f.toLinearMap.toAddMonoidHom.toMultiplicative).toAlgHom
      (groupAlgebraInvariantsTensorEquiv rho t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]

private theorem invariantsMap_comul (f : Representation.IntertwiningMap rho tau) :
    (Algebra.TensorProduct.map (groupAlgebraInvariantsAlgHom f)
        (groupAlgebraInvariantsAlgHom f)).comp
      (Bialgebra.comulAlgHom k (groupAlgebraInvariants rho)) =
    (Bialgebra.comulAlgHom k (groupAlgebraInvariants tau)).comp
      (groupAlgebraInvariantsAlgHom f) := by
  ext x
  apply (groupAlgebraInvariantsTensorEquiv tau).injective
  apply Subtype.val_injective
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    invariantsMap_tensor, groupAlgebraInvariantsTensorEquiv_comul,
    groupAlgebraInvariantsComul_apply, coe_groupAlgebraInvariantsAlgHom]
  exact AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom _) _

/-- An equivariant map of exponent groups descends to a bialgebra morphism.
Antipode compatibility is given by `BialgHom.map_antipode` and the simp lemma
`BialgHomClass.map_antipode`. -/
noncomputable def groupAlgebraInvariantsBialgHom (f : Representation.IntertwiningMap rho tau) :
    groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau :=
  BialgHom.ofAlgHom (groupAlgebraInvariantsAlgHom f)
    (invariantsMap_counit f) (invariantsMap_comul f)

/-- The algebra homomorphism underlying the descended bialgebra morphism. -/
@[simp]
theorem groupAlgebraInvariantsBialgHom_toAlgHom (f : Representation.IntertwiningMap rho tau) :
    (groupAlgebraInvariantsBialgHom f).toAlgHom = groupAlgebraInvariantsAlgHom f := (rfl)

/-- The descended bialgebra morphism agrees with the split map on invariant elements. -/
@[simp]
theorem coe_groupAlgebraInvariantsBialgHom (f : Representation.IntertwiningMap rho tau)
    (x : groupAlgebraInvariants rho) :
    (groupAlgebraInvariantsBialgHom f x : MonoidAlgebra L (Multiplicative N)) =
      MonoidAlgebra.mapDomainBialgHom L f.toLinearMap.toAddMonoidHom.toMultiplicative
        (x : MonoidAlgebra L (Multiplicative M)) := by
  rw [← BialgHom.coe_toAlgHom, groupAlgebraInvariantsBialgHom_toAlgHom,
    coe_groupAlgebraInvariantsAlgHom]

/-- Descent sends the identity exponent map to the identity bialgebra morphism. -/
@[simp]
theorem groupAlgebraInvariantsBialgHom_id :
    groupAlgebraInvariantsBialgHom (Representation.IntertwiningMap.id rho) =
      BialgHom.id k (groupAlgebraInvariants rho) := by
  apply BialgHom.coe_toAlgHom_injective
  simp

/-- Descent of bialgebra morphisms respects composition of equivariant exponent maps. -/
@[simp]
theorem groupAlgebraInvariantsBialgHom_comp (f : Representation.IntertwiningMap rho tau)
    (g : Representation.IntertwiningMap tau upsilon) :
    groupAlgebraInvariantsBialgHom (g.comp f) =
      (groupAlgebraInvariantsBialgHom g).comp (groupAlgebraInvariantsBialgHom f) := by
  apply BialgHom.coe_toAlgHom_injective
  simp

/-- The splitting isomorphisms identify scalar extension of a descended morphism with
the ordinary split group-algebra morphism. -/
@[simp]
theorem groupAlgebraInvariantsBaseChangeBialgEquiv_naturality
    (f : Representation.IntertwiningMap rho tau) :
    (groupAlgebraInvariantsBaseChangeBialgEquiv tau : _ →ₐc[L] _).comp
        (Bialgebra.TensorProduct.map (BialgHom.id L L) (groupAlgebraInvariantsBialgHom f)) =
      (MonoidAlgebra.mapDomainBialgHom L
        f.toLinearMap.toAddMonoidHom.toMultiplicative).comp
          ↑(groupAlgebraInvariantsBaseChangeBialgEquiv rho) := by
  apply BialgHom.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext'
  intro a x
  simp

end TauCeti.GaloisDescent
