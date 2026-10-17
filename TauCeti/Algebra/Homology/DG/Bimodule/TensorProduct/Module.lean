/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Scalar
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Functor

/-!
# Tensoring DG right modules with DG bimodules

An `(B, C)`-DG bimodule acts on DG right `B`-modules by the ordinary balanced tensor product:
`(M, N) ↦ M ⊗_B N`. The result is a DG right `C`-module. This file bundles that action as a
bifunctor, including its action on degree-zero closed morphisms. On pure tensors, the induced map
sends `m ⊗ n` to `f(m) ⊗ g(n)`.

The construction reuses the tensor bifunctor on DG bimodules. A right DG `B`-module is canonically
a DG `(R, B)`-bimodule, with the ground ring acting by scalars
(`TauCeti.DGRightModuleCat.toScalarBimodule`). Tensoring that bimodule with an `(B, C)`-bimodule
and forgetting the left scalar action gives the required right module.

The construction is underived and requires no flatness hypothesis. This functor is intended as
input to a future derived construction using suitable resolutions and invariance results.

## Main definitions

* `TauCeti.DGRightModuleCat.tensorBimoduleObj`: the DG right module `M ⊗_B N`.
* `TauCeti.DGRightModuleCat.tensorBimoduleFunctor`: the balanced tensor bifunctor.

## References

* B. Keller, *Deriving DG categories*, Sections 4 and 6.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.DGRightModuleCat

universe uR uB uC uM uN

variable {R : Type uR} {B : Type uB} {C : Type uC}
  [CommRing R] [Ring B] [Ring C] [Algebra R B] [Algebra R C]
  {Bₙ : ℤ → Submodule R B} {Cₙ : ℤ → Submodule R C}
  [GradedAlgebra Bₙ] [GradedAlgebra Cₙ]
  {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}
  {hB : IsDGAlgebra Bₙ dB} {hC : IsDGAlgebra Cₙ dC}

open BalancedTensorProduct

/-- The ordinary tensor product of a DG right module and a DG bimodule, retaining the outer right
action of the bimodule. -/
abbrev tensorBimoduleObj (M : DGRightModuleCat.{uR, uB, uM} hB)
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    DGRightModuleCat.{uR, uC, max uM uN} hC :=
  (DGBimoduleCat.tensorObj M.toScalarBimodule N).toDGRightModuleCat

variable {M M' M'' : DGRightModuleCat.{uR, uB, uM} hB}
  {N N' N'' : DGBimoduleCat.{uR, uB, uC, uN} hB hC}

/-- The differential on a homogeneous pure tensor has the usual Koszul sign. -/
theorem tensorBimoduleObj_differential_tmul {p : ℤ} {m : M}
    (hm : m ∈ M.grading p) (n : N) :
    (tensorBimoduleObj M N).differential (tmul R B m n) =
      tmul R B (M.differential m) n + p.negOnePow • tmul R B m (N.differential n) :=
  DGBimoduleCat.tensorObj_differential_tmul hm n

/-- A pure tensor of homogeneous elements has the sum of their degrees. -/
theorem tmul_mem_tensorBimoduleObj_grading {p q : ℤ} {m : M} {n : N}
    (hm : m ∈ M.grading p) (hn : n ∈ N.grading q) :
    tmul R B m n ∈ (tensorBimoduleObj M N).grading (p + q) :=
  DGBimoduleCat.tmul_mem_tensorObj_grading hm hn

/-- The tensor map induced by a right-module morphism and a bimodule morphism. -/
abbrev tensorBimoduleMap (f : M ⟶ M') (g : N ⟶ N') :
    tensorBimoduleObj M N ⟶ tensorBimoduleObj M' N' :=
  (DGBimoduleCat.tensorMap (toScalarBimoduleMap f) g).val

/-- On a pure tensor, the tensor morphism acts on both factors. -/
@[simp]
theorem tensorBimoduleMap_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    tensorBimoduleMap f g (tmul R B m n) = tmul R B (f m) (g n) :=
  DGBimoduleCat.tensorMap_tmul (toScalarBimoduleMap f) g m n

/-- Morphisms out of `M ⊗_B N` are determined by their values on pure tensors. -/
@[ext]
theorem tensorBimoduleObj_hom_ext {P : DGRightModuleCat.{uR, uC, max uM uN} hC}
    {f g : tensorBimoduleObj M N ⟶ P}
    (h : ∀ (m : M) (n : N), f (tmul R B m n) = g (tmul R B m n)) : f = g := by
  apply hom_ext
  intro z
  induction z using BalancedTensorProduct.induction_on with
  | ht m n => exact h m n
  | ha x y hx hy => simp only [map_add, hx, hy]

/-- Tensoring identity morphisms gives the identity. -/
@[simp]
theorem tensorBimoduleMap_id (M : DGRightModuleCat.{uR, uB, uM} hB)
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    tensorBimoduleMap (M := M) (N := N) (𝟙 M) (𝟙 N) = 𝟙 (tensorBimoduleObj M N) := by
  rw [tensorBimoduleMap, toScalarBimoduleMap_id, DGBimoduleCat.tensorMap_id]
  -- The forgetful functor acts on morphisms by `Subtype.val`; transport its identity law.
  exact DGBimoduleCat.forgetToRightModuleCat.map_id _

/-- Tensoring preserves simultaneous composition in the two factors. -/
@[simp]
theorem tensorBimoduleMap_comp (f : M ⟶ M') (g : N ⟶ N')
    (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
    tensorBimoduleMap (f ≫ f') (g ≫ g') =
      tensorBimoduleMap f g ≫ tensorBimoduleMap f' g' := by
  rw [tensorBimoduleMap, toScalarBimoduleMap_comp, DGBimoduleCat.tensorMap_comp]
  -- The forgetful functor acts on morphisms by `Subtype.val`; transport its composition law.
  exact DGBimoduleCat.forgetToRightModuleCat.map_comp _ _

/-- Tensor morphisms are additive in the module map. -/
@[simp]
theorem tensorBimoduleMap_add_left (f f' : M ⟶ M') (g : N ⟶ N') :
    tensorBimoduleMap (f + f') g = tensorBimoduleMap f g + tensorBimoduleMap f' g :=
  congrArg Subtype.val
    (DGBimoduleCat.tensorMap_add_left
      (toScalarBimoduleMap f) (toScalarBimoduleMap f') g)

/-- Tensor morphisms are additive in the bimodule map. -/
@[simp]
theorem tensorBimoduleMap_add_right (f : M ⟶ M') (g g' : N ⟶ N') :
    tensorBimoduleMap f (g + g') = tensorBimoduleMap f g + tensorBimoduleMap f g' :=
  congrArg Subtype.val
    (DGBimoduleCat.tensorMap_add_right (toScalarBimoduleMap f) g g')

/-- Tensor morphisms respect ground-ring scaling in the module map. -/
@[simp]
theorem tensorBimoduleMap_smul_left (r : R) (f : M ⟶ M') (g : N ⟶ N') :
    tensorBimoduleMap (r • f) g = r • tensorBimoduleMap f g :=
  congrArg Subtype.val
    (DGBimoduleCat.tensorMap_smul_left r (toScalarBimoduleMap f) g)

/-- Tensor morphisms respect ground-ring scaling in the bimodule map. -/
@[simp]
theorem tensorBimoduleMap_smul_right (r : R) (f : M ⟶ M') (g : N ⟶ N') :
    tensorBimoduleMap f (r • g) = r • tensorBimoduleMap f g :=
  congrArg Subtype.val
    (DGBimoduleCat.tensorMap_smul_right r (toScalarBimoduleMap f) g)

/-- Tensoring a zero map in the module factor gives zero. -/
@[simp]
theorem tensorBimoduleMap_zero_left (g : N ⟶ N') :
    tensorBimoduleMap (0 : M ⟶ M') g = 0 := by
  simpa only [zero_smul] using tensorBimoduleMap_smul_left (0 : R) (0 : M ⟶ M') g

/-- Tensoring a zero map in the bimodule factor gives zero. -/
@[simp]
theorem tensorBimoduleMap_zero_right (f : M ⟶ M') :
    tensorBimoduleMap f (0 : N ⟶ N') = 0 := by
  simpa only [zero_smul] using tensorBimoduleMap_smul_right (0 : R) f (0 : N ⟶ N')

/-- The ordinary balanced tensor product as a bifunctor from DG right modules and DG bimodules to
DG right modules: the composite of the scalar-left embedding, the DG bimodule tensor bifunctor,
and forgetting the left scalar action. The definition is exposed so that its objects and
morphisms remain definitionally `tensorBimoduleObj` and `tensorBimoduleMap`; the public statements
of `tensorBimoduleFunctor_obj_map` and `tensorBimoduleFunctor_map_app` depend on this. -/
@[expose]
def tensorBimoduleFunctor :
    CategoryTheory.Functor (DGRightModuleCat.{uR, uB, uM} hB)
      (CategoryTheory.Functor (DGBimoduleCat.{uR, uB, uC, uN} hB hC)
        (DGRightModuleCat.{uR, uC, max uM uN} hC)) :=
  toScalarBimoduleFunctor ⋙ DGBimoduleCat.tensorFunctor ⋙
    (Functor.whiskeringRight _ _ _).obj DGBimoduleCat.forgetToRightModuleCat

@[simp]
theorem tensorBimoduleFunctor_obj_obj (M : DGRightModuleCat.{uR, uB, uM} hB)
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    (tensorBimoduleFunctor.obj M).obj N = tensorBimoduleObj M N := (rfl)

@[simp]
theorem tensorBimoduleFunctor_obj_map (M : DGRightModuleCat.{uR, uB, uM} hB) (g : N ⟶ N') :
    (tensorBimoduleFunctor.obj M).map g = tensorBimoduleMap (𝟙 M) g := by
  rw [tensorBimoduleMap, toScalarBimoduleMap_id]
  -- The composite applies the forgetful functor, which acts on morphisms by `Subtype.val`.
  rfl

@[simp]
theorem tensorBimoduleFunctor_map_app (f : M ⟶ M')
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    (tensorBimoduleFunctor.map f).app N = tensorBimoduleMap f (𝟙 N) := (rfl)

/-- For a fixed right DG module `M`, the partial functor `N ↦ M ⊗_B N` is additive. -/
instance (M : DGRightModuleCat.{uR, uB, uM} hB) :
    ((tensorBimoduleFunctor.{uR, uB, uC, uM, uN} (hC := hC)).obj M).Additive :=
  (inferInstance : ((DGBimoduleCat.tensorFunctor (hC := hC)).obj M.toScalarBimodule ⋙
    DGBimoduleCat.forgetToRightModuleCat).Additive)

/-- For a fixed right DG module `M`, the partial functor `N ↦ M ⊗_B N` is `R`-linear. -/
instance (M : DGRightModuleCat.{uR, uB, uM} hB) :
    ((tensorBimoduleFunctor.{uR, uB, uC, uM, uN} (hC := hC)).obj M).Linear R :=
  (inferInstance : ((DGBimoduleCat.tensorFunctor (hC := hC)).obj M.toScalarBimodule ⋙
    DGBimoduleCat.forgetToRightModuleCat).Linear R)

/-- The tensor bifunctor is additive in the right-module variable: `M ↦ (N ↦ M ⊗_B N)` is an
additive functor into the functor category. This is the composite of additive functors. -/
instance : (tensorBimoduleFunctor.{uR, uB, uC, uM, uN}
    (hB := hB) (hC := hC)).Additive :=
  (inferInstance : (toScalarBimoduleFunctor ⋙ DGBimoduleCat.tensorFunctor ⋙
    (Functor.whiskeringRight _ _ _).obj DGBimoduleCat.forgetToRightModuleCat).Additive)

/-- The tensor bifunctor is `R`-linear in the right-module variable: `M ↦ (N ↦ M ⊗_B N)` is an
`R`-linear functor into the functor category. -/
instance : (tensorBimoduleFunctor.{uR, uB, uC, uM, uN}
    (hB := hB) (hC := hC)).Linear R where
  -- Mathlib has no `Linear` instance for `whiskeringRight`, so check this componentwise.
  map_smul _ _ := by
    apply NatTrans.ext
    funext N
    exact tensorBimoduleMap_smul_left _ _ _

end TauCeti.DGRightModuleCat
