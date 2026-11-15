/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import TauCeti.Algebra.Homology.DG.Bimodule.InternalHom.Functor
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Module

/-!
# The tensor--Hom adjunction for differential graded modules

For a differential graded `(A, B)`-bimodule `M`, ordinary balanced tensor product with `M`
is left adjoint to the internal Hom out of `M`:

`Hom_B(L ⊗_A M, N) ≃ Hom_A(L, Hom_B(M, N))`.

The equivalence sends a morphism `f` to `l ↦ (m ↦ f(l ⊗ m))`.  Its inverse evaluates a
morphism `g` on pure tensors by `l ⊗ m ↦ g(l)(m)`.  The total grading and the Koszul
differentials on the tensor product and internal Hom make both maps morphisms of DG right
modules.  No flatness hypothesis is needed because this is the underived adjunction.

The three carriers are kept in a common universe, so the internal Hom remains in that universe and
the two functors form an adjoint pair between the chosen categories of small DG modules.

## Main definitions

* `TauCeti.DGBimoduleCat.tensorHomEquiv`: the tensor--Hom equivalence on morphisms.
* `TauCeti.DGBimoduleCat.tensorInternalHomAdjunction`: the resulting adjunction.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.DGBimoduleCat

universe uR uA uB u

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

open BalancedTensorProduct DGRightModule

attribute [local instance 100] BalancedTensorProduct.rightModule
  BalancedTensorProduct.rightIsScalarTower
attribute [local instance] BalancedTensorProduct.tensorGradedOuterRight

variable {M : DGBimoduleCat.{uR, uA, uB, u} hA hB}
  {L L' : DGRightModuleCat.{uR, uA, u} hA}
  {N N' : DGRightModuleCat.{uR, uB, u} hB}

namespace TensorHom

private def curryFun (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) (l : L) :
    M →ₗ[Bᵐᵒᵖ] N where
  toFun m := f (tmul R A l m)
  map_add' x y := by rw [tmul_add, map_add]
  map_smul' b m := by
    rw [← BalancedTensorProduct.smul_tmul_right]
    simpa only [RingHom.id_apply] using map_smul f b (tmul R A l m)

@[simp]
private theorem curryFun_apply (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N)
    (l : L) (m : M) : curryFun f l m = f (tmul R A l m) := rfl

private theorem curryFun_zero (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) :
    curryFun f 0 = 0 := by
  ext m
  rw [curryFun_apply, zero_tmul]
  exact f.toLinearMap.map_zero

private theorem curryFun_add (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) (x y : L) :
    curryFun f (x + y) = curryFun f x + curryFun f y := by
  ext m
  rw [curryFun_apply, add_tmul, map_add, LinearMap.add_apply, curryFun_apply, curryFun_apply]

private theorem curryFun_mem {p : ℤ}
    (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) {l : L} (hl : l ∈ L.grading p) :
    curryFun f l ∈ dgRightModuleCochains
      (R := R) (A := B) (ℳ := M.grading) (ℳN := N.grading) p := by
  rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def]
  intro q m hm
  have h := Graded.map_mem f
    (DGRightModuleCat.tmul_mem_tensorBimoduleObj_grading hl hm)
  -- The cochain predicate views the right-linear map through restriction of scalars.
  change f (tmul R A l m) ∈ N.grading (q + p)
  simpa only [add_comm q p] using h

private def curryValue (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) (l : L) :
    M.internalHomObj N := by
  refine ⟨⟨curryFun f l, ?_⟩⟩
  induction l using DirectSum.Decomposition.inductionOn L.grading with
  | zero =>
      rw [curryFun_zero]
      exact zero_mem _
  | @homogeneous p l =>
      exact Submodule.mem_iSup_of_mem p (curryFun_mem f l.2)
  | add x y hx hy =>
      rw [curryFun_add]
      exact add_mem hx hy

@[simp]
private theorem curryValue_apply (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N)
    (l : L) (m : M) : curryValue f l m = f (tmul R A l m) := by
  rw [curryValue, DGRightModule.InternalHom.mk_apply, curryFun_apply]

@[simp]
private theorem curryValue_zero (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) :
    curryValue f 0 = 0 := by
  apply DGRightModule.InternalHom.ext
  intro m
  rw [curryValue_apply, zero_tmul, DGRightModule.InternalHom.zero_apply]
  exact f.toLinearMap.map_zero

private theorem curryValue_add (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) (x y : L) :
    curryValue f (x + y) = curryValue f x + curryValue f y := by
  apply DGRightModule.InternalHom.ext
  intro m
  rw [curryValue_apply, DGRightModule.InternalHom.add_apply, curryValue_apply,
    curryValue_apply, add_tmul, map_add]

private theorem curryValue_mem {p : ℤ}
    (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) {l : L} (hl : l ∈ L.grading p) :
    curryValue f l ∈ DGRightModule.InternalHom.grading 𝒜 B M.grading N.grading p := by
  have h := curryFun_mem f hl
  rw [dgRightModuleCochains.mem_iff, LinearMap.isHomogeneous_def] at h
  rw [DGRightModule.InternalHom.mem_grading_iff, dgRightModuleCochains.mem_iff,
    LinearMap.isHomogeneous_def]
  intro q m hm
  -- The internal-Hom wrapper and `curryFun` have the same evaluation map.
  change curryValue f l m ∈ N.grading (q + p)
  rw [curryValue_apply]
  exact h q m hm

private def curryLinearMap (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) :
    L →ₗ[Aᵐᵒᵖ] M.internalHomObj N where
  toFun := curryValue f
  map_add' x y := by
    exact curryValue_add f x y
  map_smul' a l := by
    apply DGRightModule.InternalHom.ext
    intro m
    rw [curryValue_apply, DGRightModule.InternalHom.op_smul_apply, curryValue_apply]
    exact congrArg f (balance R A a.unop l m)

@[simp]
private theorem curryLinearMap_apply (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N)
    (l : L) (m : M) : curryLinearMap f l m = f (tmul R A l m) := by
  exact curryValue_apply f l m

private theorem map_d_tmul {p : ℤ}
    (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) {l : L} (hl : l ∈ L.grading p) (m : M) :
    N.differential (f (tmul R A l m)) =
      f (tmul R A (L.differential l) m) +
        p.negOnePow • f (tmul R A l (M.differential m)) := by
  rw [DGRightModuleCat.map_d f,
    DGRightModuleCat.tensorBimoduleObj_differential_tmul hl, map_add]
  exact congrArg _ (map_zsmul_unit f.toLinearMap p.negOnePow _)

/-- Currying a DG module morphism out of a balanced tensor product. -/
private def curry (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) :
    L ⟶ M.internalHomObj N where
  toLinearMap := curryLinearMap f
  map_mem' := curryValue_mem f
  map_d' l := by
    -- The morphism structures expose `curryValue` only after unfolding their linear maps.
    change DGRightModule.InternalHom.differential 𝒜 M.isDGRightModule N.isDGRightModule
      (curryValue f l) = curryValue f (L.differential l)
    induction l using DirectSum.Decomposition.inductionOn L.grading with
    | zero => rw [curryValue_zero, map_zero, map_zero, curryValue_zero]
    | @homogeneous p l =>
        apply DGRightModule.InternalHom.ext
        intro m
        rw [DGRightModule.InternalHom.differential_apply_of_mem _ _
          (curryValue_mem f l.2), curryValue_apply, curryValue_apply, curryValue_apply,
          map_d_tmul f l.2]
        exact add_sub_cancel_right _ _
    | add x y hx hy => rw [curryValue_add, map_add, hx, map_add, curryValue_add, hy]

@[simp]
private theorem curry_apply (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) (l : L) (m : M) :
    curry f l m = f (tmul R A l m) := curryLinearMap_apply f l m

private def uncurryBilinear (g : L ⟶ M.internalHomObj N) : L →ₗ[R] M →ₗ[R] N where
  toFun l := (DGRightModule.InternalHom.coeLM (g l)).restrictScalars R
  map_add' x y := by
    ext m
    simp
  map_smul' r l := by
    ext m
    -- Coercing the restricted linear map exposes evaluation of the internal-Hom element.
    change (g (r • l)) m = r • (g l) m
    have hg : g (r • l) = r • g l := g.toLinearMap.map_smul_of_tower r l
    rw [hg, DGRightModule.InternalHom.smul_apply]

@[simp]
private theorem uncurryBilinear_apply (g : L ⟶ M.internalHomObj N) (l : L) (m : M) :
    uncurryBilinear g l m = g l m := (rfl)

private theorem uncurryBilinear_balanced (g : L ⟶ M.internalHomObj N)
    (a : A) (l : L) (m : M) :
    uncurryBilinear g (op a • l) m = uncurryBilinear g l (a • m) := by
  rw [uncurryBilinear_apply, map_smul, DGRightModule.InternalHom.op_smul_apply,
    uncurryBilinear_apply, unop_op]

private def uncurryLinearMap (g : L ⟶ M.internalHomObj N) :
    DGRightModuleCat.tensorBimoduleObj L M →ₗ[Bᵐᵒᵖ] N where
  toFun := lift (uncurryBilinear g) (uncurryBilinear_balanced g)
  map_add' := map_add _
  map_smul' b z := BalancedTensorProduct.lift_smul_right Bᵐᵒᵖ
    (uncurryBilinear g) (uncurryBilinear_balanced g)
    (fun b l m ↦ map_smul (g l) b m) b z

@[simp]
private theorem uncurryLinearMap_tmul (g : L ⟶ M.internalHomObj N) (l : L) (m : M) :
    uncurryLinearMap g (tmul R A l m) = g l m := by
  -- The right-linear wrapper has the balanced lift as its underlying function.
  change lift (uncurryBilinear g) (uncurryBilinear_balanced g) (tmul R A l m) = _
  rw [lift_tmul, uncurryBilinear_apply]

local instance : SetLike.GradedSMul
    (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (InternalGrading.ofDecomposition L.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul 𝒜
    (InternalGrading.ofDecomposition M.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Uncurrying a DG module morphism into an internal Hom. -/
private def uncurry (g : L ⟶ M.internalHomObj N) :
    DGRightModuleCat.tensorBimoduleObj L M ⟶ N where
  toLinearMap := uncurryLinearMap g
  map_mem' {p z} hz := by
    have h := map_mem_of_tmul (R := R) (A := A) (M := L) (N := M) (𝒜 := 𝒜)
      (InternalGrading.ofDecomposition L.grading)
      (InternalGrading.ofDecomposition M.grading) N.grading
      (lift (uncurryBilinear g) (uncurryBilinear_balanced g)) 0
      (fun {q r} {l m} hl hm ↦ by
        have hl' : l ∈ L.grading q := by
          simpa only [InternalGrading.ofDecomposition_piece] using hl
        have hm' : m ∈ M.grading r := by
          simpa only [InternalGrading.ofDecomposition_piece] using hm
        have hg := DGRightModule.InternalHom.map_mem_of_mem_grading
          (Graded.map_mem g hl') hm'
        rw [lift_tmul, uncurryBilinear_apply]
        simpa only [add_zero, add_comm r q] using hg)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hz)
    -- `uncurryLinearMap` is the right-linear structure on this balanced lift.
    change lift (uncurryBilinear g) (uncurryBilinear_balanced g) z ∈ N.grading p
    simpa only [add_zero] using h
  map_d' z := by
    induction z using BalancedTensorProduct.induction_on with
    | ht l m =>
        induction l using DirectSum.Decomposition.inductionOn L.grading with
        | zero => simp
        | @homogeneous p l =>
            have h := congrArg (fun k ↦ k m) (DGRightModuleCat.map_d g l)
            rw [DGRightModule.InternalHom.differential_apply_of_mem _ _
              (Graded.map_mem g l.2)] at h
            rw [uncurryLinearMap_tmul, DGRightModuleCat.tensorBimoduleObj_differential_tmul l.2,
              map_add, uncurryLinearMap_tmul, map_zsmul_unit, uncurryLinearMap_tmul]
            exact eq_add_of_sub_eq h
        | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | ha x y hx hy => simp only [map_add, hx, hy]

@[simp]
private theorem uncurry_tmul (g : L ⟶ M.internalHomObj N) (l : L) (m : M) :
    uncurry g (tmul R A l m) = g l m := by
  exact uncurryLinearMap_tmul g l m

end TensorHom

open TensorHom

/-- **The tensor--Hom equivalence** for DG modules.  A morphism
`L ⊗_A M ⟶ N` corresponds to the morphism `L ⟶ Hom_B(M, N)` obtained by currying. -/
def tensorHomEquiv (L : DGRightModuleCat.{uR, uA, u} hA)
    (N : DGRightModuleCat.{uR, uB, u} hB) :
    (DGRightModuleCat.tensorBimoduleObj L M ⟶ N) ≃ (L ⟶ M.internalHomObj N) where
  toFun := curry
  invFun := uncurry
  left_inv f := by
    apply DGRightModuleCat.tensorBimoduleObj_hom_ext
    intro l m
    rw [uncurry_tmul, curry_apply]
  right_inv g := by
    apply DGRightModuleCat.hom_ext
    intro l
    apply DGRightModule.InternalHom.ext
    intro m
    rw [curry_apply, uncurry_tmul]

/-- The tensor--Hom equivalence evaluates a curried morphism on `l` and `m` by applying the
original morphism to `l ⊗ m`. -/
@[simp]
theorem tensorHomEquiv_apply_apply
    (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) (l : L) (m : M) :
    tensorHomEquiv (M := M) L N f l m = f (tmul R A l m) := curry_apply f l m

/-- The inverse tensor--Hom equivalence evaluates on a pure tensor by applying the internal-Hom
morphism twice. -/
@[simp]
theorem tensorHomEquiv_symm_apply_tmul (g : L ⟶ M.internalHomObj N) (l : L) (m : M) :
    (tensorHomEquiv (M := M) L N).symm g (tmul R A l m) = g l m := uncurry_tmul g l m

/-- The tensor--Hom equivalence is natural in the source module. -/
theorem tensorHomEquiv_naturality_left (f : L' ⟶ L)
    (g : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) :
    tensorHomEquiv (M := M) L' N
        (DGRightModuleCat.tensorBimoduleMap f (𝟙 M) ≫ g) =
      f ≫ tensorHomEquiv (M := M) L N g := by
  apply DGRightModuleCat.hom_ext
  intro l
  apply DGRightModule.InternalHom.ext
  intro m
  rw [tensorHomEquiv_apply_apply, DGRightModuleCat.comp_apply,
    DGRightModuleCat.tensorBimoduleMap_tmul, DGBimoduleCat.id_apply,
    DGRightModuleCat.comp_apply, tensorHomEquiv_apply_apply]

/-- The tensor--Hom equivalence is natural in the target module. -/
theorem tensorHomEquiv_naturality_right
    (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) (g : N ⟶ N') :
    tensorHomEquiv (M := M) L N' (f ≫ g) =
      tensorHomEquiv (M := M) L N f ≫ M.internalHom.map g := by
  apply DGRightModuleCat.hom_ext
  intro l
  apply DGRightModule.InternalHom.ext
  intro m
  rw [tensorHomEquiv_apply_apply, DGRightModuleCat.comp_apply,
    DGRightModuleCat.comp_apply, DGBimoduleCat.internalHom_map_apply,
    tensorHomEquiv_apply_apply]

/-- **Tensoring with a DG bimodule is left adjoint to its internal Hom functor.** -/
def tensorInternalHomAdjunction :
    DGRightModuleCat.tensorBimoduleFunctor.flip.obj M ⊣ M.internalHom :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv (M := M)
      homEquiv_naturality_left_symm := fun f g ↦ by
        -- Unfold the flipped bifunctor at this component to expose its tensor map.
        change (tensorHomEquiv (M := M) _ _).symm (f ≫ g) =
          DGRightModuleCat.tensorBimoduleMap f (𝟙 M) ≫
            (tensorHomEquiv (M := M) _ _).symm g
        apply DGRightModuleCat.tensorBimoduleObj_hom_ext
        intro l m
        rw [DGRightModuleCat.comp_apply, DGRightModuleCat.tensorBimoduleMap_tmul,
          DGBimoduleCat.id_apply, tensorHomEquiv_symm_apply_tmul,
          tensorHomEquiv_symm_apply_tmul,
          DGRightModuleCat.comp_apply]
      homEquiv_naturality_right := tensorHomEquiv_naturality_right (M := M) }

/-- The hom-set equivalence of the tensor--internal-Hom adjunction is `tensorHomEquiv`. -/
@[simp]
theorem tensorInternalHomAdjunction_homEquiv
    (L : DGRightModuleCat.{uR, uA, u} hA) (N : DGRightModuleCat.{uR, uB, u} hB) :
    (tensorInternalHomAdjunction (M := M)).homEquiv L N = tensorHomEquiv (M := M) L N := by
  rw [tensorInternalHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- The unit of the tensor--internal-Hom adjunction sends `l` to `m ↦ l ⊗ m`. -/
-- Evaluate before `simp` unfolds the functor composites in the coercion's type.
@[simp↓]
theorem tensorInternalHomAdjunction_unit_app_apply_apply
    (L : DGRightModuleCat.{uR, uA, u} hA) (l : L) (m : M) :
    DFunLike.coe (F := M.internalHomObj (DGRightModuleCat.tensorBimoduleObj L M))
      ((tensorInternalHomAdjunction (M := M)).unit.app L l) m = tmul R A l m := by
  rw [← Adjunction.homEquiv_id, tensorInternalHomAdjunction_homEquiv]
  exact (tensorHomEquiv_apply_apply (M := M) (𝟙 _) l m).trans
    (by rw [DGRightModuleCat.id_apply])

/-- The counit of the tensor--internal-Hom adjunction is evaluation. -/
-- Evaluate before `simp` unfolds the functor composites in the coercion's type.
@[simp↓]
theorem tensorInternalHomAdjunction_counit_app_tmul
    (N : DGRightModuleCat.{uR, uB, u} hB) (g : M.internalHomObj N) (m : M) :
    (tensorInternalHomAdjunction (M := M)).counit.app N (tmul R A g m) = g m := by
  rw [← Adjunction.homEquiv_symm_id, tensorInternalHomAdjunction_homEquiv]
  exact (tensorHomEquiv_symm_apply_tmul (M := M) (𝟙 _) g m).trans
    (congrArg (fun k ↦ k m) (DGRightModuleCat.id_apply _ g))

end TauCeti.DGBimoduleCat
