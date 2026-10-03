/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.BaseChange.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor-product scalar extension of skew-zigzag algebras

For a finite simple graph without isolated vertices and a commutative-ring algebra `k → l`,
scalar extension of the skew-zigzag relation quotient is the quotient over `l` with every
backtrack ratio mapped along `algebraMap k l`. The comparison
`l ⊗[k] Z_k(G,c) ≃ₐ[l] Z_l(G,c.map)` sends `a ⊗ x` to `a` times the existing coefficient map.

The comparison uses the vertex, arrow and chosen-backtrack bases to prove bijectivity. No
flatness or injectivity assumption is imposed on the coefficient map, and no incident-edge
choice appears in the public comparison. This concerns the relation quotients, not the
componentwise ordinary algebra's exceptional dual-number factors at isolated vertices.

## References

* C. Couture, *Skew-Zigzag Algebras*, Section 3, for the parameterized presentations and bases.
* The construction uses Mathlib's `AlgHom.liftEquiv` and `Module.Basis.baseChange`.
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
      a • skewZigzagBaseChange G (algebraMap k l) c x :=
  (rfl)

omit [Algebra k l] in
/-- The coefficient map respects the vertex, arrow and chosen-volume basis family. -/
@[simp]
theorem skewZigzagBaseChange_skewZigzagBasisFun (f : k →+* l)
    (t : ∀ i : V, {j : V // G.Adj i j}) (b : ZigzagBasisIndex G) :
    skewZigzagBaseChange G f c (skewZigzagBasisFun k G c t b) =
      skewZigzagBasisFun l G (c.map (f : k →* l)) t b := by
  rcases b with i | d | i
  · rw [skewZigzagBasisFun_inl, skewZigzagBasisFun_inl, vertexIdempotent_eq_ofPath,
      skewZigzagBaseChange_skewZigzagMk_ofPath, vertexIdempotent_eq_ofPath]
  · rw [skewZigzagBasisFun_inr_inl, skewZigzagBasisFun_inr_inl,
      ofArrow_eq_ofPath_arrowPath, skewZigzagBaseChange_skewZigzagMk_ofPath,
      ofArrow_eq_ofPath_arrowPath]
  · rw [skewZigzagBasisFun_inr_inr, skewZigzagBasisFun_inr_inr, skewZigzagVolume_def,
      skewZigzagVolume_def, backtrackElem_eq_ofPath,
      skewZigzagBaseChange_skewZigzagMk_ofPath, backtrackElem_eq_ofPath]

/-- The tensor-product comparison is bijective for a graph without isolated vertices,
over arbitrary commutative coefficient rings. -/
theorem skewZigzagScalarExtension_bijective (hns : ∀ i : V, ∃ j, G.Adj i j) :
    Function.Bijective (skewZigzagScalarExtension (l := l) G c) := by
  classical
  let t : ∀ i : V, {j : V // G.Adj i j} := fun i => ⟨(hns i).choose, (hns i).choose_spec⟩
  let b := (skewZigzagBasis k G c t).baseChange l
  let b' := skewZigzagBasis l G (c.map (algebraMap k l : k →* l)) t
  have he : (skewZigzagScalarExtension G c).toLinearMap =
      (b.equiv b' (Equiv.refl _)).toLinearMap := by
    apply b.ext
    intro i
    rw [LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply]
    simp only [b, b', Module.Basis.baseChange_apply, AlgHom.toLinearMap_apply,
      skewZigzagScalarExtension_tmul, skewZigzagBasis_apply,
      skewZigzagBaseChange_skewZigzagBasisFun, one_smul, Equiv.refl_apply]
  have hbij : Function.Bijective (skewZigzagScalarExtension (l := l) G c).toLinearMap := by
    rw [he]
    exact (b.equiv b' (Equiv.refl _)).bijective
  exact hbij

/-- Scalar extension of a skew-zigzag relation quotient is the quotient with extended
parameters. The map is canonical, independent of the incident edges used to prove bijectivity. -/
noncomputable def skewZigzagScalarExtensionEquiv (hns : ∀ i : V, ∃ j, G.Adj i j) :
    l ⊗[k] skewZigzagQuotient k G c ≃ₐ[l]
      skewZigzagQuotient l G (c.map (algebraMap k l : k →* l)) :=
  AlgEquiv.ofBijective (skewZigzagScalarExtension G c)
    (skewZigzagScalarExtension_bijective (l := l) G c hns)

/-- The algebra equivalence has the canonical scalar-extension homomorphism as its map. -/
@[simp]
theorem skewZigzagScalarExtensionEquiv_toAlgHom (hns : ∀ i : V, ∃ j, G.Adj i j) :
    (skewZigzagScalarExtensionEquiv (l := l) G c hns).toAlgHom =
      skewZigzagScalarExtension G c :=
  (rfl)

/-- The scalar-extension equivalence on pure tensors. -/
@[simp]
theorem skewZigzagScalarExtensionEquiv_tmul (hns : ∀ i : V, ∃ j, G.Adj i j)
    (a : l) (x : skewZigzagQuotient k G c) :
    skewZigzagScalarExtensionEquiv G c hns (a ⊗ₜ[k] x) =
      a • skewZigzagBaseChange G (algebraMap k l) c x :=
  (rfl)

/-- The inverse comparison carries a coefficient image to the corresponding unit pure tensor. -/
@[simp]
theorem skewZigzagScalarExtensionEquiv_symm_baseChange
    (hns : ∀ i : V, ∃ j, G.Adj i j) (x : skewZigzagQuotient k G c) :
    (skewZigzagScalarExtensionEquiv G c hns).symm
      (skewZigzagBaseChange G (algebraMap k l) c x) = 1 ⊗ₜ[k] x := by
  apply (skewZigzagScalarExtensionEquiv G c hns).injective
  rw [AlgEquiv.apply_symm_apply, skewZigzagScalarExtensionEquiv_tmul, one_smul]

/-- The inverse scalar-extension equivalence carries a path class to its unit pure tensor. -/
@[simp]
theorem skewZigzagScalarExtensionEquiv_symm_skewZigzagMk_ofPath
    (hns : ∀ i : V, ∃ j, G.Adj i j) (p : Quiver.TotalPath (DoubledQuiver G)) :
    (skewZigzagScalarExtensionEquiv G c hns).symm
      (skewZigzagMk l G (c.map (algebraMap k l : k →* l)) (ofPath p)) =
        1 ⊗ₜ[k] skewZigzagMk k G c (ofPath p) := by
  apply (skewZigzagScalarExtensionEquiv G c hns).injective
  rw [AlgEquiv.apply_symm_apply, skewZigzagScalarExtensionEquiv_tmul,
    skewZigzagBaseChange_skewZigzagMk_ofPath, one_smul]

end TauCeti
