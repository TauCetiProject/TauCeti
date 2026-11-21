/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Pontryagin.Basic
public import TauCeti.Topology.PathSpace.Moore.Comparison.Trans

/-!
# Pontryagin products of families of loops

Let `f : A → Ω_x X` and `g : B → Ω_x X` be continuous families of loops on the unit interval at a
point `x` of a space `X`. Read in the Moore loop space `Ωᴹ_x X`, a topological monoid, through
`Path.toMooreLoop`, they push classes `a ∈ H_i(A; k)` and `b ∈ H_j(B; k)` forward to classes whose
Pontryagin product is the image of the cross product `a × b` under the family of products
`(a, b) ↦ f a * g b` (`TauCeti.map_mulMooreLoop_comp_prodMap_singularHomologyCross`). By
`Path.homotopic_mooreLoopTrans_comp_prodMap`, this family is homotopic to the family of Moore loops
of the concatenations `(f a).trans (g b)`.

## Main declarations

* `TauCeti.tensorHom_comp_mul_eq_mulMooreLoop_comp_prodMap`: the family `(a, b) ↦ f a * g b` is the
  tensor product of `f` and `g`, read in the Moore loops, followed by the multiplication.
* `TauCeti.map_mulMooreLoop_comp_prodMap_singularHomologyCross`: the family
  `(a, b) ↦ f a * g b` carries a cross product to a Pontryagin product.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory MonObj AlgebraicTopology TopCat
open scoped TensorProduct

namespace TauCeti

universe u

variable {X : Type u} [TopologicalSpace X] {x : X} {A B : Type u} [TopologicalSpace A]
  [TopologicalSpace B]

/-- For families of loops `f` and `g`, the map `(a, b) ↦ f a * g b` into the Moore loops is the
tensor product of `f` and `g`, read in the Moore loops, followed by the multiplication of the Moore
loop space. -/
theorem tensorHom_comp_mul_eq_mulMooreLoop_comp_prodMap (f : C(A, Path x x))
    (g : C(B, Path x x)) :
    (ofHom ((MooreLoopSpace.homotopyEquivPath x).symm.toFun.comp f) ⊗ₘ
      ofHom ((MooreLoopSpace.homotopyEquivPath x).symm.toFun.comp g)) ≫
        μ[TopCat.of (MooreLoopSpace X x)] =
      (ofHom ((Path.mulMooreLoop x).comp (f.prodMap g)) : TopCat.of A ⊗ TopCat.of B ⟶ _) := by
  refine ConcreteCategory.hom_ext _ _ fun y ↦ ?_
  rw [ConcreteCategory.comp_apply, of_mul_apply, TopCat.tensor_apply]
  exact (congrArg₂ (· * ·) (MooreLoopSpace.homotopyEquivPath_symm_apply _)
    (MooreLoopSpace.homotopyEquivPath_symm_apply _)).trans
      (Path.mulMooreLoop_apply (f y.1, g y.2)).symm

/-- **Families of loops carry a cross product to a Pontryagin product.** For families of loops
`f : A → Ω_x X` and `g : B → Ω_x X` and classes `a ∈ H_i(A; k)` and `b ∈ H_j(B; k)`, the map
`(a, b) ↦ f a * g b` into the Moore loops at `x` sends the cross product `a × b` to the Pontryagin
product `f_* a · g_* b`. -/
theorem map_mulMooreLoop_comp_prodMap_singularHomologyCross (k : Type u) [CommRing k]
    (f : C(A, Path x x)) (g : C(B, Path x x)) {i j n : ℕ} (h : i + j = n)
    (a : ((singularHomologyFunctor (ModuleCat.{u} k) i).obj (𝟙_ _)).obj (TopCat.of A))
    (b : ((singularHomologyFunctor (ModuleCat.{u} k) j).obj (𝟙_ _)).obj (TopCat.of B)) :
    ((singularHomologyFunctor (ModuleCat.{u} k) n).obj (𝟙_ _)).map (X := TopCat.of A ⊗ TopCat.of B)
        (ofHom ((Path.mulMooreLoop x).comp (f.prodMap g)))
        (((singularHomologyFunctor (ModuleCat.{u} k) n).map (λ_ (𝟙_ _)).hom).app
          (TopCat.of A ⊗ TopCat.of B)
          (singularHomologyCross (C := ModuleCat.{u} k) (TopCat.of A) (TopCat.of B) (𝟙_ _) (𝟙_ _)
            i j n h (a ⊗ₜ b))) =
      pontryaginMul k (TopCat.of (MooreLoopSpace X x)) i j n h
        (((singularHomologyFunctor (ModuleCat.{u} k) i).obj (𝟙_ _)).map
          (ofHom ((MooreLoopSpace.homotopyEquivPath x).symm.toFun.comp f)) a)
        (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (𝟙_ _)).map
          (ofHom ((MooreLoopSpace.homotopyEquivPath x).symm.toFun.comp g)) b) := by
  rw [pontryaginMul_map_map, tensorHom_comp_mul_eq_mulMooreLoop_comp_prodMap]

end TauCeti
