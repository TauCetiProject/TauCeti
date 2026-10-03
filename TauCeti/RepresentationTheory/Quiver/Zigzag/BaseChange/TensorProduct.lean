/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.BaseChange.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor-product scalar extension of skew-zigzag algebras

For a finite simple graph and a commutative-ring algebra `k → l`,
scalar extension of the skew-zigzag relation quotient is the quotient over `l` with every
backtrack ratio mapped along `algebraMap k l`. The comparison
`l ⊗[k] Z_k(G,c) ≃ₐ[l] Z_l(G,c.map)` sends `a ⊗ x` to `a` times the existing coefficient map.

No flatness or injectivity assumption is imposed on the coefficient map, and no incident-edge
choice appears in the comparison. At an isolated vertex the relation quotient has a single
vertex class. This concerns the relation quotients, not the componentwise ordinary algebra's
exceptional dual-number factors at isolated vertices.

## References

* C. Couture, *Skew-Zigzag Algebras*, Section 3, for the parameterized presentations and bases.
-/

public section

noncomputable section

namespace TauCeti

open scoped TensorProduct
open PathAlgebra DoubledQuiver

universe u w z

variable {k : Type w} {l : Type z} [CommRing k] [CommRing l] [Algebra k l]
  {V : Type u} (G : SimpleGraph V) [Finite V] (c : SkewZigzagParameter k G)

-- Restrict the target's scalar action only for the tensor-product universal property.
private abbrev coefficientAlgebra : Algebra k
    (skewZigzagQuotient l G (c.map (algebraMap k l : k →* l))) :=
  Algebra.compHom _ (algebraMap k l)

attribute [local instance] coefficientAlgebra

private abbrev coefficientScalarTower : IsScalarTower k l
    (skewZigzagQuotient l G (c.map (algebraMap k l : k →* l))) :=
  IsScalarTower.of_algebraMap_eq' rfl

attribute [local instance] coefficientScalarTower

private noncomputable def coefficientAlgHom :
    skewZigzagQuotient k G c →ₐ[k]
      skewZigzagQuotient l G (c.map (algebraMap k l : k →* l)) where
  __ := skewZigzagBaseChange G (algebraMap k l) c
  commutes' a := by
    exact (skewZigzagBaseChange_algebraMap G (algebraMap k l) c a).trans
      (IsScalarTower.algebraMap_apply k l _ a).symm

/-- The canonical scalar-extension comparison, sending `a ⊗ x` to `a` times the
coefficient image of `x`. The parameter over `l` is obtained by mapping each ratio. -/
noncomputable def skewZigzagScalarExtension :
    l ⊗[k] skewZigzagQuotient k G c →ₐ[l]
      skewZigzagQuotient l G (c.map (algebraMap k l : k →* l)) :=
  AlgHom.liftEquiv k l _ _ (coefficientAlgHom G c)

/-- The scalar-extension comparison on pure tensors. -/
@[simp]
theorem skewZigzagScalarExtension_tmul (a : l) (x : skewZigzagQuotient k G c) :
    skewZigzagScalarExtension G c (a ⊗ₜ[k] x) =
      a • skewZigzagBaseChange G (algebraMap k l) c x := by
  exact AlgHom.liftEquiv_tmul (coefficientAlgHom G c) a x

-- Use the path-algebra universal property, as in `PathAlgebra.baseChangeAlgHom`,
-- with unit pure tensors as the assigned path values.
private noncomputable def tensorPathAlgHom :
    pathAlgebra l (DoubledQuiver G) →ₐ[l] l ⊗[k] skewZigzagQuotient k G c := by
  let g : pathAlgebra k (DoubledQuiver G) →ₐ[k] l ⊗[k] skewZigzagQuotient k G c :=
    Algebra.TensorProduct.includeRight.comp (skewZigzagMk k G c)
  refine liftAlgHom l (fun p => g (ofPath p)) ?_ ?_ ?_
  · intro a b d p q
    rw [← map_mul, ofPath_mul_ofPath_of_comp]
  · intro p q hpq
    rw [← map_mul, ofPath_mul_ofPath_of_not_composable hpq, map_zero]
  · let _ := Fintype.ofFinite (DoubledQuiver G)
    rw [← map_sum]
    simp only [← vertexIdempotent_eq_ofPath, ← one_def, map_one]

private theorem tensorPathAlgHom_ofPath (p : Quiver.TotalPath (DoubledQuiver G)) :
    tensorPathAlgHom (l := l) G c (ofPath p) = 1 ⊗ₜ[k] skewZigzagMk k G c (ofPath p) := by
  dsimp only [tensorPathAlgHom]
  refine liftAlgHom_ofPath l _ ?_ ?_ _ p
  · intro a b d p q
    rw [← map_mul, ofPath_mul_ofPath_of_comp]
  · intro p q hpq
    rw [← map_mul, ofPath_mul_ofPath_of_not_composable hpq, map_zero]

private theorem tensorPathAlgHom_relator (x : pathAlgebra l (DoubledQuiver G))
    (hx : IsSkewZigzagRelator l G (c.map (algebraMap k l : k →* l)) x) :
    tensorPathAlgHom G c x = 0 := by
  cases hx with
  | nonreturn p hlen hne =>
      rw [tensorPathAlgHom_ofPath,
        skewZigzagMk_ofPath_eq_zero_of_ne k G c p hlen hne, TensorProduct.tmul_zero]
  | backtrack_ratio h h' =>
      simp only [map_sub, map_smul, backtrackElem_eq_ofPath, tensorPathAlgHom_ofPath]
      simp only [← backtrackElem_eq_ofPath, sub_eq_zero]
      rw [skewZigzagMk_backtrackElem_eq_smul k G c h h']
      simp only [SkewZigzagParameter.map_ratio, Units.coe_map, MonoidHom.coe_ofClass,
        TensorProduct.tmul_smul]
      simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | long_path p hlen =>
      rw [tensorPathAlgHom_ofPath,
        skewZigzagMk_ofPath_eq_zero_of_three_le k G c p hlen, TensorProduct.tmul_zero]

private noncomputable def scalarExtensionInverse :
    skewZigzagQuotient l G (c.map (algebraMap k l : k →* l)) →ₐ[l]
      l ⊗[k] skewZigzagQuotient k G c :=
  skewZigzagLift l G (c.map (algebraMap k l : k →* l)) (tensorPathAlgHom G c)
    (tensorPathAlgHom_relator G c)

private theorem scalarExtensionInverse_ofPath (p : Quiver.TotalPath (DoubledQuiver G)) :
    scalarExtensionInverse (l := l) G c
      (skewZigzagMk l G (c.map (algebraMap k l : k →* l)) (ofPath p)) =
        1 ⊗ₜ[k] skewZigzagMk k G c (ofPath p) := by
  rw [scalarExtensionInverse, skewZigzagLift_skewZigzagMk, tensorPathAlgHom_ofPath]

/-- The tensor-product comparison is bijective for every finite graph,
over arbitrary commutative coefficient rings. -/
theorem skewZigzagScalarExtension_bijective :
    Function.Bijective (skewZigzagScalarExtension (l := l) G c) := by
  have hleft : (scalarExtensionInverse G c).comp (skewZigzagScalarExtension G c) =
      AlgHom.id l (l ⊗[k] skewZigzagQuotient k G c) := by
    apply Algebra.TensorProduct.ext_ring
    apply (AlgHom.cancel_right (skewZigzagMk_surjective k G c)).mp
    apply PathAlgebra.algHom_ext k
    intro p
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply]
    simp only [skewZigzagScalarExtension_tmul, one_smul,
      skewZigzagBaseChange_skewZigzagMk_ofPath, scalarExtensionInverse_ofPath]
  have hright : (skewZigzagScalarExtension G c).comp (scalarExtensionInverse G c) =
      AlgHom.id l (skewZigzagQuotient l G (c.map (algebraMap k l : k →* l))) := by
    apply (AlgHom.cancel_right
      (skewZigzagMk_surjective l G (c.map (algebraMap k l : k →* l)))).mp
    apply PathAlgebra.algHom_ext l
    intro p
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    simp only [scalarExtensionInverse_ofPath, skewZigzagScalarExtension_tmul,
      one_smul, skewZigzagBaseChange_skewZigzagMk_ofPath]
  exact ⟨Function.LeftInverse.injective (AlgHom.congr_fun hleft),
    Function.RightInverse.surjective (AlgHom.congr_fun hright)⟩

/-- Scalar extension of a skew-zigzag relation quotient is the quotient with extended
parameters, for every finite graph. No choice of incident edges is required. -/
noncomputable def skewZigzagScalarExtensionEquiv :
    l ⊗[k] skewZigzagQuotient k G c ≃ₐ[l]
      skewZigzagQuotient l G (c.map (algebraMap k l : k →* l)) :=
  AlgEquiv.ofBijective (skewZigzagScalarExtension G c)
    (skewZigzagScalarExtension_bijective (l := l) G c)

/-- The algebra equivalence has the canonical scalar-extension homomorphism as its map. -/
@[simp]
theorem skewZigzagScalarExtensionEquiv_toAlgHom :
    (skewZigzagScalarExtensionEquiv (l := l) G c).toAlgHom =
      skewZigzagScalarExtension G c := by
  exact AlgEquiv.toAlgHom_ofBijective _ _

/-- The scalar-extension equivalence on pure tensors. -/
@[simp]
theorem skewZigzagScalarExtensionEquiv_tmul
    (a : l) (x : skewZigzagQuotient k G c) :
    skewZigzagScalarExtensionEquiv G c (a ⊗ₜ[k] x) =
      a • skewZigzagBaseChange G (algebraMap k l) c x := by
  rw [skewZigzagScalarExtensionEquiv, AlgEquiv.ofBijective_apply,
    skewZigzagScalarExtension_tmul]

/-- The inverse comparison carries a coefficient image to the corresponding unit pure tensor. -/
@[simp]
theorem skewZigzagScalarExtensionEquiv_symm_baseChange
    (x : skewZigzagQuotient k G c) :
    (skewZigzagScalarExtensionEquiv G c).symm
      (skewZigzagBaseChange G (algebraMap k l) c x) = 1 ⊗ₜ[k] x := by
  apply (skewZigzagScalarExtensionEquiv G c).injective
  rw [AlgEquiv.apply_symm_apply, skewZigzagScalarExtensionEquiv_tmul, one_smul]

/-- The inverse scalar-extension equivalence carries a path class to its unit pure tensor. -/
@[simp]
theorem skewZigzagScalarExtensionEquiv_symm_skewZigzagMk_ofPath
    (p : Quiver.TotalPath (DoubledQuiver G)) :
    (skewZigzagScalarExtensionEquiv G c).symm
      (skewZigzagMk l G (c.map (algebraMap k l : k →* l)) (ofPath p)) =
        1 ⊗ₜ[k] skewZigzagMk k G c (ofPath p) := by
  apply (skewZigzagScalarExtensionEquiv G c).injective
  rw [AlgEquiv.apply_symm_apply, skewZigzagScalarExtensionEquiv_tmul,
    skewZigzagBaseChange_skewZigzagMk_ofPath, one_smul]

end TauCeti
