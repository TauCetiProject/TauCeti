/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Prism
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Action

/-!
# Equivariant cubical prisms

An equivariant homotopy gives a homotopy of right modules over the cubical chain algebra,
not just a homotopy of complexes over the coefficient ring. The prism uses time as its first
coordinate, before both the space and acting-monoid coordinates. Consequently it commutes
with the right chain action without a sign.

`cubicalChainModulePrism` is the degree-minus-one operator in cohomological grading. Its
boundary is the difference of the endpoint maps. `cubicalChainModulePrismLinearMap` bundles
its linearity over the acting chain algebra when every time slice is equivariant.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapters II and VII.
-/

public noncomputable section

open MulOpposite

namespace TauCeti

universe u

variable {X Y : Type u} {G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (R : Type*) [CommRing R] {f g : C(X, Y)}

/-- The cubical prism, extended to the direct sum of all chain dimensions. -/
def cubicalChainModulePrism (H : f.Homotopy g) :
    cubicalChainModule X G R →ₗ[R] cubicalChainModule Y G R :=
  cubicalChainModuleDesc fun n ↦
    (cubicalChainModuleLof Y G R (n + 1)).comp (NormalizedCubicalChain.prism R H n)

variable {R}

/-- On a homogeneous chain the module prism is the normalized cubical prism. -/
@[simp]
theorem cubicalChainModulePrism_lof (H : f.Homotopy g) {n : ℕ}
    (c : NormalizedCubicalChain X R n) :
    cubicalChainModulePrism (G := G) R H (cubicalChainModuleLof X G R n c) =
      cubicalChainModuleLof Y G R (n + 1) (NormalizedCubicalChain.prism R H n c) :=
  cubicalChainModuleDesc_lof _ c

/-- The prism lowers cohomological degree by one. -/
theorem cubicalChainModulePrism_mem (H : f.Homotopy g) {i : ℤ}
    {x : cubicalChainModule X G R} (hx : x ∈ cubicalChainModuleGrading X G R i) :
    cubicalChainModulePrism R H x ∈ cubicalChainModuleGrading Y G R (i - 1) := by
  rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
  · simp only [map_zero, Submodule.zero_mem]
  · rw [cubicalChainModulePrism_lof]
    exact mem_cubicalChainModuleGrading_iff.2
      (Or.inr ⟨n + 1, _, by push_cast; omega, rfl⟩)

/-- The boundary of the module prism is the difference of the endpoint push-forwards. -/
theorem cubicalChainModuleDifferential_prism_add_prism_differential (H : f.Homotopy g)
    (x : cubicalChainModule X G R) :
    cubicalChainModuleDifferential Y G R (cubicalChainModulePrism R H x) +
        cubicalChainModulePrism R H (cubicalChainModuleDifferential X G R x) =
      cubicalChainModuleLinearMap R g x - cubicalChainModuleLinearMap R f x := by
  induction x using cubicalChainModule.induction_on with
  | add x y hx hy =>
    simp only [map_add]
    rw [add_add_add_comm, hx, hy]
    abel
  | lof n c =>
    rw [cubicalChainModulePrism_lof, cubicalChainModuleDifferential_lof_succ,
      cubicalChainModuleLinearMap_lof, cubicalChainModuleLinearMap_lof]
    cases n with
    | zero =>
      rw [cubicalChainModuleDifferential_lof_zero, map_zero, add_zero,
        NormalizedCubicalChain.boundary_prism_zero, map_sub]
    | succ n =>
      rw [cubicalChainModuleDifferential_lof_succ, cubicalChainModulePrism_lof, ← map_add,
        NormalizedCubicalChain.boundary_prism_add_prism_boundary, map_sub]

section Action

variable [TopologicalSpace G] [SMul Gᵐᵒᵖ X] [ContinuousSMul Gᵐᵒᵖ X]
  [SMul Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y]

/-- An equivariant prism commutes with the right action of homogeneous chains. The cast
only identifies the two parenthesizations of the number of coordinates. -/
theorem NormalizedCubicalChain.prism_act (H : f.Homotopy g)
    (hH : ∀ (t : unitInterval) (a : G) (x : X), H (t, op a • x) = op a • H (t, x))
    {p q : ℕ}
    (c : NormalizedCubicalChain X R p) (a : NormalizedCubicalChain G R q) :
    NormalizedCubicalChain.cast R (by omega : (p + q) + 1 = (p + 1) + q)
        (NormalizedCubicalChain.prism R H (p + q)
          (NormalizedCubicalChain.act X G R p q c a)) =
      NormalizedCubicalChain.act Y G R (p + 1) q
        (NormalizedCubicalChain.prism R H p c) a := by
  induction c using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, LinearMap.add_apply]
  | smul r c hc => simp only [map_smul, hc, LinearMap.smul_apply]
  | ofCube c =>
    induction a using NormalizedCubicalChain.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul r a ha => simp only [map_smul, ha]
    | ofCube a =>
      simp only [NormalizedCubicalChain.act_def, NormalizedCubicalChain.crossProduct_ofCube,
        NormalizedCubicalChain.map_ofCube, NormalizedCubicalChain.prism_ofCube,
        map_neg, LinearMap.neg_apply]
      congr 1
      rw [NormalizedCubicalChain.ofCube_def, NormalizedCubicalChain.cast_mk,
        CubicalChain.cast_single, ← NormalizedCubicalChain.ofCube_def]
      apply congrArg (NormalizedCubicalChain.ofCube Y R)
      ext x
      simp only [SingularCube.cast_apply, SingularCube.prism_apply,
        ContinuousMap.comp_apply, SingularCube.crossProduct_apply, actMap_apply, hH]
      congr 3
      funext i
      simp only [Fin.tail, Function.comp_def]
      congr 1
      apply Fin.ext
      simp
      omega

end Action

section MonoidAction

variable [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [MulAction Gᵐᵒᵖ X] [ContinuousSMul Gᵐᵒᵖ X]
  [MulAction Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y]

/-- The prism of an equivariant homotopy is linear over the right chain-algebra action. -/
theorem cubicalChainModulePrism_op_smul (H : f.Homotopy g)
    (hH : ∀ (t : unitInterval) (a : G) (x : X), H (t, op a • x) = op a • H (t, x))
    (a : normalizedCubicalChainAlgebra G R) (x : cubicalChainModule X G R) :
    cubicalChainModulePrism R H (op a • x) = op a • cubicalChainModulePrism R H x := by
  induction x using cubicalChainModule.induction_on with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | lof p c =>
    induction a using DirectSum.induction_on with
    | zero => simp
    | add a b ha hb => simp only [op_add, add_smul, map_add, ha, hb]
    | of q a =>
      rw [← DirectSum.lof_eq_of R, op_lof_smul_cubicalChainModuleLof,
        cubicalChainModulePrism_lof, cubicalChainModulePrism_lof,
        op_lof_smul_cubicalChainModuleLof, ← NormalizedCubicalChain.prism_act H hH,
        cubicalChainModuleLof_cast]

/-- The prism of an equivariant homotopy as a right chain-algebra linear map. It has
cohomological degree minus one, rather than being a morphism of DG modules. -/
def cubicalChainModulePrismLinearMap (H : f.Homotopy g)
    (hH : ∀ (t : unitInterval) (a : G) (x : X), H (t, op a • x) = op a • H (t, x)) :
    cubicalChainModule X G R →ₗ[(normalizedCubicalChainAlgebra G R)ᵐᵒᵖ]
      cubicalChainModule Y G R where
  toFun := cubicalChainModulePrism R H
  map_add' := map_add _
  map_smul' a x := by
    rw [← op_unop a]
    exact cubicalChainModulePrism_op_smul H hH a.unop x

/-- The bundled equivariant prism has the same values as the coefficient-linear prism. -/
@[simp]
theorem cubicalChainModulePrismLinearMap_apply (H : f.Homotopy g)
    (hH : ∀ (t : unitInterval) (a : G) (x : X), H (t, op a • x) = op a • H (t, x))
    (x : cubicalChainModule X G R) :
    cubicalChainModulePrismLinearMap H hH x = cubicalChainModulePrism R H x := (rfl)

end MonoidAction

end TauCeti
