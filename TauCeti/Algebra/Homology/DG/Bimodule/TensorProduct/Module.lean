/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Functor

/-!
# Tensoring DG right modules with DG bimodules

An `(B, C)`-DG bimodule acts on DG right `B`-modules by the ordinary balanced tensor product:
`(M, N) ↦ M ⊗_B N`. The result is a DG right `C`-module. This file bundles that action as a
bifunctor, including its action on degree-zero closed morphisms. On pure tensors, the induced map
sends `m ⊗ n` to `f(m) ⊗ g(n)`.

The construction reuses the tensor bifunctor on DG bimodules. A right DG `B`-module is canonically
a DG `(R, B)`-bimodule, with the ground ring acting by scalars. Tensoring that bimodule with an
`(B, C)`-bimodule and forgetting the left scalar action gives the required right module.

The construction is underived and requires no flatness hypothesis. Its derived version is
obtained by resolving the module input before applying this functor.

## Main definitions

* `TauCeti.DGRightModuleCat.toScalarBimodule`: a right DG module as a DG bimodule over the ground
  ring on the left.
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

/-- Scalar multiplication by the trivially graded ground ring preserves every homogeneous piece
of a DG module. -/
local instance scalarGradedSMul (M : DGRightModuleCat.{uR, uB, uM} hB) :
    SetLike.GradedSMul (trivialGrading R R) M.grading where
  smul_mem := by
    intro p q r m hr hm
    rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
    · simpa using (M.grading q).smul_mem r hm
    · simp

/-- A DG right module over `B`, regarded as a DG `(R, B)`-bimodule through the scalar action of
the ground ring on the left. -/
abbrev toScalarBimodule (M : DGRightModuleCat.{uR, uB, uM} hB) :
    DGBimoduleCat (isDGAlgebra_trivialGrading R) hB where
  toDGRightModuleCat := M
  isDGLeftModule :=
    { isHomogeneous := M.isDGRightModule.isHomogeneous
      sq_zero := M.isDGRightModule.sq_zero
      leibniz := by
        intro p r hr m
        rcases (mem_trivialGrading_iff R R).mp hr with rfl | rfl
        · simp
        · simp }

@[simp]
theorem toScalarBimodule_carrier (M : DGRightModuleCat.{uR, uB, uM} hB) :
    M.toScalarBimodule.carrier = M.carrier := (rfl)

@[simp]
theorem toScalarBimodule_grading (M : DGRightModuleCat.{uR, uB, uM} hB) :
    M.toScalarBimodule.grading = M.grading := (rfl)

@[simp]
theorem toScalarBimodule_differential (M : DGRightModuleCat.{uR, uB, uM} hB) :
    M.toScalarBimodule.differential = M.differential := (rfl)

/-- A right-module morphism as the corresponding morphism of scalar-left bimodules. -/
abbrev toScalarBimoduleMap {M M' : DGRightModuleCat.{uR, uB, uM} hB} (f : M ⟶ M') :
    M.toScalarBimodule ⟶ M'.toScalarBimodule := by
  refine ⟨f, ?_⟩
  rw [mem_dgBimoduleHomSubmodule]
  exact fun r m ↦ f.toLinearMap.map_smul_of_tower r m

@[simp]
theorem toScalarBimoduleMap_apply {M M' : DGRightModuleCat.{uR, uB, uM} hB}
    (f : M ⟶ M') (m : M) : toScalarBimoduleMap f m = f m := (rfl)

@[simp]
theorem toScalarBimoduleMap_id (M : DGRightModuleCat.{uR, uB, uM} hB) :
    toScalarBimoduleMap (𝟙 M) = 𝟙 M.toScalarBimodule := by
  ext m
  change M at m
  rw [toScalarBimoduleMap_apply (f := 𝟙 M) (m := m)]
  exact (DGRightModuleCat.id_apply M m).trans
    (DGBimoduleCat.id_apply M.toScalarBimodule m).symm

@[simp]
theorem toScalarBimoduleMap_comp {M M' M'' : DGRightModuleCat.{uR, uB, uM} hB}
    (f : M ⟶ M') (g : M' ⟶ M'') :
    toScalarBimoduleMap (f ≫ g) = toScalarBimoduleMap f ≫ toScalarBimoduleMap g := by
  ext m
  change M at m
  rw [toScalarBimoduleMap_apply (f := f ≫ g) (m := m),
    DGBimoduleCat.comp_apply,
    toScalarBimoduleMap_apply (f := f) (m := m),
    toScalarBimoduleMap_apply (f := g) (m := f m)]
  exact DGRightModuleCat.comp_apply f g m

/-- Viewing right DG modules as scalar-left DG bimodules is a faithful linear functor. -/
abbrev toScalarBimoduleFunctor :
    CategoryTheory.Functor (DGRightModuleCat.{uR, uB, uM} hB)
      (DGBimoduleCat.{uR, uR, uB, uM} (isDGAlgebra_trivialGrading R) hB) where
  obj := toScalarBimodule
  map := toScalarBimoduleMap
  map_id := toScalarBimoduleMap_id
  map_comp := toScalarBimoduleMap_comp

@[simp]
theorem toScalarBimoduleFunctor_obj (M : DGRightModuleCat.{uR, uB, uM} hB) :
    toScalarBimoduleFunctor.obj M = M.toScalarBimodule := (rfl)

@[simp]
theorem toScalarBimoduleFunctor_map {M M' : DGRightModuleCat.{uR, uB, uM} hB} (f : M ⟶ M') :
    toScalarBimoduleFunctor.map f = toScalarBimoduleMap f := (rfl)

instance : (toScalarBimoduleFunctor.{uR, uB, uM} (hB := hB)).Faithful where
  map_injective h := by
    apply hom_ext
    intro m
    exact DFunLike.congr_fun h m

instance : (toScalarBimoduleFunctor.{uR, uB, uM} (hB := hB)).Additive where
  map_add := by
    intro M M' f g
    ext m
    rfl

instance : (toScalarBimoduleFunctor.{uR, uB, uM} (hB := hB)).Linear R where
  map_smul := by
    intro M M' r f
    ext m
    rfl

/-- The ordinary tensor product of a DG right module and a DG bimodule, retaining the outer right
action of the bimodule. -/
abbrev tensorBimoduleObj (M : DGRightModuleCat.{uR, uB, uM} hB)
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    DGRightModuleCat.{uR, uC, max uM uN} hC :=
  (DGBimoduleCat.tensorObj M.toScalarBimodule N).toDGRightModuleCat

variable {M M' M'' : DGRightModuleCat.{uR, uB, uM} hB}
  {N N' N'' : DGBimoduleCat.{uR, uB, uC, uN} hB hC}

/-- The tensor map induced by a right-module morphism and a bimodule morphism. -/
abbrev tensorBimoduleMap (f : M ⟶ M') (g : N ⟶ N') :
    tensorBimoduleObj M N ⟶ tensorBimoduleObj M' N' :=
  (DGBimoduleCat.tensorMap (toScalarBimoduleMap f) g).val

/-- On a pure tensor, the tensor morphism acts on both factors. -/
@[simp]
theorem tensorBimoduleMap_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    tensorBimoduleMap f g (tmul R B m n) = tmul R B (f m) (g n) :=
  DGBimoduleCat.tensorMap_tmul (toScalarBimoduleMap f) g m n

/-- Tensoring identity morphisms gives the identity. -/
@[simp]
theorem tensorBimoduleMap_id (M : DGRightModuleCat.{uR, uB, uM} hB)
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    tensorBimoduleMap (M := M) (N := N) (𝟙 M) (𝟙 N) = 𝟙 (tensorBimoduleObj M N) := by
  apply hom_ext
  intro z
  induction z using BalancedTensorProduct.induction_on with
  | ht m n =>
      change M at m
      change DGBimoduleCat.tensorMap (toScalarBimoduleMap (𝟙 M)) (𝟙 N)
        (tmul R B m n) = (𝟙 (tensorBimoduleObj M N)) (tmul R B m n)
      rw [DGBimoduleCat.tensorMap_tmul]
      rw [toScalarBimoduleMap_apply (f := 𝟙 M) (m := m),
        DGRightModuleCat.id_apply, DGBimoduleCat.id_apply,
        DGRightModuleCat.id_apply]
  | ha x y hx hy => simp only [map_add, hx, hy]

/-- Tensoring preserves simultaneous composition in the two factors. -/
@[simp]
theorem tensorBimoduleMap_comp (f : M ⟶ M') (g : N ⟶ N')
    (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
    tensorBimoduleMap (f ≫ f') (g ≫ g') =
      tensorBimoduleMap f g ≫ tensorBimoduleMap f' g' := by
  apply hom_ext
  intro z
  induction z using BalancedTensorProduct.induction_on with
  | ht m n =>
      change M at m
      change DGBimoduleCat.tensorMap (toScalarBimoduleMap (f ≫ f')) (g ≫ g')
        (tmul R B m n) =
          (tensorBimoduleMap f g ≫ tensorBimoduleMap f' g') (tmul R B m n)
      rw [DGBimoduleCat.tensorMap_tmul]
      rw [toScalarBimoduleMap_apply (f := f ≫ f') (m := m),
        DGRightModuleCat.comp_apply, DGBimoduleCat.comp_apply,
        DGRightModuleCat.comp_apply, tensorBimoduleMap_tmul,
        tensorBimoduleMap_tmul]
  | ha x y hx hy => simp only [map_add, hx, hy]

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
DG right modules. -/
abbrev tensorBimoduleFunctor :
    CategoryTheory.Functor (DGRightModuleCat.{uR, uB, uM} hB)
      (CategoryTheory.Functor (DGBimoduleCat.{uR, uB, uC, uN} hB hC)
        (DGRightModuleCat.{uR, uC, max uM uN} hC)) where
  obj M :=
    { obj := tensorBimoduleObj M
      map := fun g ↦ tensorBimoduleMap (𝟙 M) g
      map_id := fun N ↦ tensorBimoduleMap_id M N
      map_comp := fun g g' ↦ by
        simpa using tensorBimoduleMap_comp (𝟙 M) g (𝟙 M) g' }
  map f :=
    { app := fun N ↦ tensorBimoduleMap f (𝟙 N)
      naturality := fun N N' g ↦ by
        rw [← tensorBimoduleMap_comp, ← tensorBimoduleMap_comp]
        simp }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact tensorBimoduleMap_id M N
  map_comp f f' := by
    apply NatTrans.ext
    funext N
    simpa using tensorBimoduleMap_comp f (𝟙 N) f' (𝟙 N)

@[simp]
theorem tensorBimoduleFunctor_obj_obj (M : DGRightModuleCat.{uR, uB, uM} hB)
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    (tensorBimoduleFunctor.obj M).obj N = tensorBimoduleObj M N := (rfl)

@[simp]
theorem tensorBimoduleFunctor_obj_map (M : DGRightModuleCat.{uR, uB, uM} hB) (g : N ⟶ N') :
    (tensorBimoduleFunctor.obj M).map g = tensorBimoduleMap (𝟙 M) g := (rfl)

@[simp]
theorem tensorBimoduleFunctor_map_app (f : M ⟶ M')
    (N : DGBimoduleCat.{uR, uB, uC, uN} hB hC) :
    (tensorBimoduleFunctor.map f).app N = tensorBimoduleMap f (𝟙 N) := (rfl)

instance (M : DGRightModuleCat.{uR, uB, uM} hB) :
    ((tensorBimoduleFunctor (hC := hC)).obj M).Additive where
  map_add := by intros; unfold tensorBimoduleFunctor; exact tensorBimoduleMap_add_right _ _ _

instance (M : DGRightModuleCat.{uR, uB, uM} hB) :
    ((tensorBimoduleFunctor (hC := hC)).obj M).Linear R where
  map_smul := by intros; unfold tensorBimoduleFunctor; exact tensorBimoduleMap_smul_right _ _ _

instance : (tensorBimoduleFunctor.{uR, uB, uC, uM, uN}
    (hB := hB) (hC := hC)).Additive where
  map_add := by
    intros
    apply NatTrans.ext
    funext N
    unfold tensorBimoduleFunctor
    exact tensorBimoduleMap_add_left _ _ _

instance : (tensorBimoduleFunctor.{uR, uB, uC, uM, uN}
    (hB := hB) (hC := hC)).Linear R where
  map_smul := by
    intros
    apply NatTrans.ext
    funext N
    unfold tensorBimoduleFunctor
    exact tensorBimoduleMap_smul_left _ _ _

end TauCeti.DGRightModuleCat
