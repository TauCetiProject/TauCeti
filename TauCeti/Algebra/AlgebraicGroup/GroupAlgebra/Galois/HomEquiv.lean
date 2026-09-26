/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Map
public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Character

/-!
# Recovering morphisms from Galois-equivariant characters

For a finite Galois extension `L/k`, descent of group algebras is fully faithful:
Hopf algebra morphisms between the descended coordinate algebras correspond bijectively
to equivariant homomorphisms of the exponent groups. The inverse takes the map on group-like
elements after scalar extension and uses the canonical character comparisons.

This supplies the morphism part of the character-group classification of groups of
multiplicative type split by `L`, including tori. The exponent groups need not be finitely
generated or torsion-free.

Under the character comparison of `Galois.Character`, the descended morphisms of
`Galois.Map` induce the original equivariant maps on exponent groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open scoped TensorProduct
open TauCeti TauCeti.GaloisDescent Representation.IntertwiningMap

namespace BialgHom

variable {k L M N : Type*} [Field k] [Field L] [Algebra k L]
variable [FiniteDimensional k L] [IsGalois k L] [AddCommGroup M] [AddCommGroup N]
variable {rho : Representation ℤ (L ≃ₐ[k] L) M}
variable {tau : Representation ℤ (L ≃ₐ[k] L) N}

/-- The additive character map underlying the recovered equivariant map. -/
private noncomputable def invariantsCharacterAddHom
    (F : groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau) : M →+ N :=
  AddMonoidHom.mk' (fun m ↦
    (groupAlgebraInvariantsCharacterEquiv tau
      (TauCeti.GroupLike.map (Bialgebra.TensorProduct.map (BialgHom.id L L) F)
        ((groupAlgebraInvariantsCharacterEquiv rho).symm (Multiplicative.ofAdd m)))).toAdd)
    (by intro x y; simp)

/-- The equivariant map of exponent groups recovered from a morphism of descended Hopf algebras.
It is the map on characters after extending scalars to the splitting field. -/
noncomputable def groupAlgebraInvariantsCharacterMap
    (F : groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau) :
    Representation.IntertwiningMap rho tau where
  toLinearMap := (invariantsCharacterAddHom F).toIntLinearMap
  isIntertwining' sigma := by
    ext m
    simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap,
      invariantsCharacterAddHom, AddMonoidHom.mk'_apply]
    have h := smul_groupAlgebraInvariantsCharacterEquiv_symm_apply rho sigma
      (Multiplicative.ofAdd m)
    simp only [toAdd_ofAdd] at h
    rw [← h, ScalarAut.groupLikeMap_smul, groupAlgebraInvariantsCharacterEquiv_smul]
    rfl

/-- Evaluation of the recovered map in terms of the canonical character comparisons. -/
@[simp]
theorem groupAlgebraInvariantsCharacterMap_apply
    (F : groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau) (m : M) :
    F.groupAlgebraInvariantsCharacterMap m =
      (groupAlgebraInvariantsCharacterEquiv tau
        (TauCeti.GroupLike.map (Bialgebra.TensorProduct.map (BialgHom.id L L) F)
          ((groupAlgebraInvariantsCharacterEquiv rho).symm (Multiplicative.ofAdd m)))).toAdd :=
  (rfl)

end BialgHom

namespace Representation.IntertwiningMap

variable {k L M N : Type*} [Field k] [Field L] [Algebra k L]
variable [FiniteDimensional k L] [IsGalois k L] [AddCommGroup M] [AddCommGroup N]
variable {rho : Representation ℤ (L ≃ₐ[k] L) M}
variable {tau : Representation ℤ (L ≃ₐ[k] L) N}

/-- The character comparison is natural for descended morphisms: their map on characters
is the original equivariant map on exponents. -/
@[simp]
theorem groupAlgebraInvariantsCharacterEquiv_map
    (f : Representation.IntertwiningMap rho tau)
    (x : GroupLike L (L ⊗[k] groupAlgebraInvariants rho)) :
    groupAlgebraInvariantsCharacterEquiv tau
        (TauCeti.GroupLike.map
          (Bialgebra.TensorProduct.map (BialgHom.id L L) f.groupAlgebraInvariantsBialgHom) x) =
      Multiplicative.ofAdd (f (groupAlgebraInvariantsCharacterEquiv rho x).toAdd) := by
  rw [groupAlgebraInvariantsCharacterEquiv_apply_eq_iff, TauCeti.GroupLike.val_map]
  have h := DFunLike.congr_fun (groupAlgebraInvariantsBaseChangeBialgEquiv_naturality f) x.val
  simp only [BialgHom.comp_apply, BialgEquiv.coe_toBialgHom] at h
  rw [h, (groupAlgebraInvariantsCharacterEquiv_apply_eq_iff rho x _).mp rfl]
  exact MonoidAlgebra.mapDomain_single

/-- Recovering the character map of a descended morphism returns the original map. -/
@[simp]
theorem groupAlgebraInvariantsCharacterMap_groupAlgebraInvariantsBialgHom
    (f : Representation.IntertwiningMap rho tau) :
    f.groupAlgebraInvariantsBialgHom.groupAlgebraInvariantsCharacterMap = f := by
  ext m
  simp

end Representation.IntertwiningMap

namespace BialgHom

variable {k L M N : Type*} [Field k] [Field L] [Algebra k L]
variable [FiniteDimensional k L] [IsGalois k L] [AddCommGroup M] [AddCommGroup N]
variable {rho : Representation ℤ (L ≃ₐ[k] L) M}
variable {tau : Representation ℤ (L ≃ₐ[k] L) N}

/-- Scalar extension of a descended morphism in the split group-algebra coordinates. -/
private noncomputable def splitInvariantsMap
    (F : groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau) :
    MonoidAlgebra L (Multiplicative M) →ₐc[L] MonoidAlgebra L (Multiplicative N) :=
  (groupAlgebraInvariantsBaseChangeBialgEquiv tau).toBialgHom.comp
    ((Bialgebra.TensorProduct.map (BialgHom.id L L) F).comp
      (groupAlgebraInvariantsBaseChangeBialgEquiv rho).symm.toBialgHom)

private theorem splitInvariantsMap_single
    (F : groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau) (m : Multiplicative M) :
    splitInvariantsMap F (MonoidAlgebra.single m 1) =
      MonoidAlgebra.single (Multiplicative.ofAdd (F.groupAlgebraInvariantsCharacterMap m.toAdd))
        1 := by
  have h := (groupAlgebraInvariantsCharacterEquiv_apply_eq_iff tau
    (TauCeti.GroupLike.map (Bialgebra.TensorProduct.map (BialgHom.id L L) F)
      ((groupAlgebraInvariantsCharacterEquiv rho).symm m)) _).mp rfl
  simpa only [splitInvariantsMap, BialgHom.comp_apply, BialgEquiv.toBialgHom_eq_coe,
    BialgEquiv.coe_toBialgHom, TauCeti.GroupLike.val_map,
    groupAlgebraInvariantsCharacterEquiv_symm_apply_val,
    groupAlgebraInvariantsCharacterMap_apply, ofAdd_toAdd] using h

private theorem splitInvariantsMap_apply_invariant
    (F : groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau)
    (x : groupAlgebraInvariants rho) :
    splitInvariantsMap F (x : MonoidAlgebra L (Multiplicative M)) =
      (F x : MonoidAlgebra L (Multiplicative N)) := by
  simp only [splitInvariantsMap, BialgHom.comp_apply, BialgEquiv.toBialgHom_eq_coe,
    BialgEquiv.coe_toBialgHom,
    groupAlgebraInvariantsBaseChangeBialgEquiv_symm_apply, Bialgebra.TensorProduct.map_tmul,
    BialgHom.id_apply, groupAlgebraInvariantsBaseChangeBialgEquiv_tmul, one_smul]

private theorem splitInvariantsMap_injective :
    Function.Injective (splitInvariantsMap (rho := rho) (tau := tau)) := by
  intro F G h
  apply BialgHom.ext
  intro x
  apply Subtype.val_injective
  have hx := DFunLike.congr_fun h (x : MonoidAlgebra L (Multiplicative M))
  simpa only [splitInvariantsMap_apply_invariant] using hx

/-- Descending the recovered character map returns the original Hopf algebra morphism.
In particular, every morphism between the descended groups is induced by a character map. -/
@[simp]
theorem groupAlgebraInvariantsBialgHom_groupAlgebraInvariantsCharacterMap
    (F : groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau) :
    F.groupAlgebraInvariantsCharacterMap.groupAlgebraInvariantsBialgHom = F := by
  apply splitInvariantsMap_injective
  apply BialgHom.coe_toAlgHom_injective
  apply MonoidAlgebra.algHom_ext
  · intro m
    simp only [BialgHom.coe_toAlgHom, splitInvariantsMap_single,
      groupAlgebraInvariantsCharacterMap_groupAlgebraInvariantsBialgHom]
  · ext

end BialgHom

namespace Representation

variable {k L M N : Type*} [Field k] [Field L] [Algebra k L]
variable [FiniteDimensional k L] [IsGalois k L] [AddCommGroup M] [AddCommGroup N]

/-- **Full faithfulness of finite Galois descent for group algebras.** Equivariant homomorphisms
of exponent groups correspond bijectively to morphisms of their descended coordinate Hopf
algebras. No finiteness or torsion-freeness assumption on the exponent groups is needed. -/
noncomputable def groupAlgebraInvariantsBialgHomEquiv
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (tau : Representation ℤ (L ≃ₐ[k] L) N) :
    Representation.IntertwiningMap rho tau ≃
      (groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau) where
  toFun := Representation.IntertwiningMap.groupAlgebraInvariantsBialgHom
  invFun := BialgHom.groupAlgebraInvariantsCharacterMap
  left_inv :=
    Representation.IntertwiningMap.groupAlgebraInvariantsCharacterMap_groupAlgebraInvariantsBialgHom
  right_inv := BialgHom.groupAlgebraInvariantsBialgHom_groupAlgebraInvariantsCharacterMap

/-- The forward correspondence is the descended group-algebra morphism. -/
@[simp]
theorem groupAlgebraInvariantsBialgHomEquiv_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (tau : Representation ℤ (L ≃ₐ[k] L) N)
    (f : Representation.IntertwiningMap rho tau) :
    groupAlgebraInvariantsBialgHomEquiv rho tau f = f.groupAlgebraInvariantsBialgHom := (rfl)

/-- The inverse correspondence is the map on characters over the splitting field. -/
@[simp]
theorem groupAlgebraInvariantsBialgHomEquiv_symm_apply
    (rho : Representation ℤ (L ≃ₐ[k] L) M) (tau : Representation ℤ (L ≃ₐ[k] L) N)
    (F : groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau) :
    (groupAlgebraInvariantsBialgHomEquiv rho tau).symm F =
      F.groupAlgebraInvariantsCharacterMap := (rfl)

end Representation

namespace BialgHom

variable {k L M N P : Type*} [Field k] [Field L] [Algebra k L]
variable [FiniteDimensional k L] [IsGalois k L]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable {rho : Representation ℤ (L ≃ₐ[k] L) M}
variable {tau : Representation ℤ (L ≃ₐ[k] L) N}
variable {upsilon : Representation ℤ (L ≃ₐ[k] L) P}

/-- The identity Hopf morphism induces the identity character map. -/
@[simp]
theorem groupAlgebraInvariantsCharacterMap_id :
    (BialgHom.id k (groupAlgebraInvariants rho)).groupAlgebraInvariantsCharacterMap =
      Representation.IntertwiningMap.id rho := by
  apply (Representation.groupAlgebraInvariantsBialgHomEquiv rho rho).injective
  simp

/-- Recovery of character maps respects composition. -/
@[simp]
theorem groupAlgebraInvariantsCharacterMap_comp
    (G : groupAlgebraInvariants tau →ₐc[k] groupAlgebraInvariants upsilon)
    (F : groupAlgebraInvariants rho →ₐc[k] groupAlgebraInvariants tau) :
    (G.comp F).groupAlgebraInvariantsCharacterMap =
      G.groupAlgebraInvariantsCharacterMap.comp F.groupAlgebraInvariantsCharacterMap := by
  apply (Representation.groupAlgebraInvariantsBialgHomEquiv rho upsilon).injective
  simp

end BialgHom
