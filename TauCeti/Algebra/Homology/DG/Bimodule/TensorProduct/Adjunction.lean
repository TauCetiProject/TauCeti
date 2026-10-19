/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import TauCeti.Algebra.Homology.DG.Bimodule.InternalHom.Functor
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Module
import TauCeti.Algebra.Ring.NegOnePow

/-!
# The tensor--Hom adjunction for differential graded modules

For a differential graded `(A, B)`-bimodule `M`, ordinary balanced tensor product with `M`
is left adjoint to the internal Hom out of `M`:

`Hom_B(L ⊗_A M, N) ≃ Hom_A(L, Hom_B(M, N))`.

The equivalence sends a morphism `f` to `l ↦ (m ↦ f(l ⊗ m))`.  Its inverse evaluates a
morphism `g` on pure tensors by `l ⊗ m ↦ g(l)(m)`.  The total grading and the Koszul
differentials on the tensor product and internal Hom make both maps morphisms of DG right
modules.  No flatness hypothesis is needed because this is the underived adjunction.

The three carriers are kept in a common universe.  This is the natural categorical formulation:
both tensor product and internal Hom then remain endofunctors between the chosen categories of
small DG modules.

## Main definitions

* `TauCeti.DGBimoduleCat.tensorRightModule`: tensoring DG right modules with a fixed DG
  bimodule.
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

variable (M : DGBimoduleCat.{uR, uA, uB, u} hA hB)

/-- Tensoring a DG right `A`-module with the fixed DG `(A, B)`-bimodule `M`. -/
abbrev tensorRightModule :
    DGRightModuleCat.{uR, uA, u} hA ⥤ DGRightModuleCat.{uR, uB, u} hB where
  obj L := DGRightModuleCat.tensorBimoduleObj L M
  map f := DGRightModuleCat.tensorBimoduleMap f (𝟙 M)
  map_id L := DGRightModuleCat.tensorBimoduleMap_id L M
  map_comp f g := by
    simpa using DGRightModuleCat.tensorBimoduleMap_comp f (𝟙 M) g (𝟙 M)

@[simp]
theorem tensorRightModule_obj (L : DGRightModuleCat.{uR, uA, u} hA) :
    (M.tensorRightModule).obj L = DGRightModuleCat.tensorBimoduleObj L M := (rfl)

@[simp]
theorem tensorRightModule_map {L L' : DGRightModuleCat.{uR, uA, u} hA} (f : L ⟶ L') :
    M.tensorRightModule.map f = DGRightModuleCat.tensorBimoduleMap f (𝟙 M) := (rfl)

variable {M}
  {L L' : DGRightModuleCat.{uR, uA, u} hA}
  {N N' : DGRightModuleCat.{uR, uB, u} hB}

namespace TensorHom

private def curryValue (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) (l : L) :
    M.internalHomObj N := by
  let φ : M →ₗ[Bᵐᵒᵖ] N :=
    { toFun := fun m ↦ f (tmul R A l m)
      map_add' := fun x y ↦ by rw [tmul_add, map_add]
      map_smul' := fun b m ↦ by
        change f (tmul R A l (b • m)) = _
        rw [← BalancedTensorProduct.smul_tmul_right]
        simpa only [RingHom.id_apply] using map_smul f b (tmul R A l m) }
  refine ⟨⟨φ, ?_⟩⟩
  induction l using DirectSum.Decomposition.inductionOn L.grading with
  | zero =>
      convert zero_mem (⨆ p, dgRightModuleCochains (R := R) (A := B)
        (ℳ := M.grading) (ℳN := N.grading) p) using 1
      ext m
      change f (tmul R A 0 m) = 0
      rw [zero_tmul]
      exact f.toLinearMap.map_zero
  | @homogeneous p l =>
      refine Submodule.mem_iSup_of_mem p (dgRightModuleCochains.mem_iff.2 ?_)
      rw [LinearMap.isHomogeneous_def]
      intro q m hm
      have h := Graded.map_mem f
        (DGRightModuleCat.tmul_mem_tensorBimoduleObj_grading l.2 hm)
      simpa only [φ, LinearMap.restrictScalars_apply, LinearMap.coe_mk, AddHom.coe_mk,
        add_comm q p] using h
  | add x y hx hy =>
      convert add_mem hx hy using 1
      ext m
      simp [φ, add_tmul]

@[simp]
private theorem curryValue_apply (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N)
    (l : L) (m : M) : curryValue f l m = f (tmul R A l m) := by
  unfold curryValue
  rw [DGRightModule.InternalHom.mk_apply]
  rfl

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
  rw [DGRightModule.InternalHom.mem_grading_iff, dgRightModuleCochains.mem_iff,
    LinearMap.isHomogeneous_def]
  intro q m hm
  have h := Graded.map_mem f
    (DGRightModuleCat.tmul_mem_tensorBimoduleObj_grading hl hm)
  change curryValue f l m ∈ N.grading (q + p)
  rw [curryValue_apply]
  simpa only [add_comm q p] using h

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
  rw [show curryLinearMap f l = curryValue f l from rfl, curryValue_apply]

/-- Currying a DG module morphism out of a balanced tensor product. -/
private def curry (f : DGRightModuleCat.tensorBimoduleObj L M ⟶ N) :
    L ⟶ M.internalHomObj N where
  toLinearMap := curryLinearMap f
  map_mem' := curryValue_mem f
  map_d' l := by
    change DGRightModule.InternalHom.differential 𝒜 M.isDGRightModule N.isDGRightModule
      (curryValue f l) = curryValue f (L.differential l)
    induction l using DirectSum.Decomposition.inductionOn L.grading with
    | zero => rw [curryValue_zero, map_zero, map_zero, curryValue_zero]
    | @homogeneous p l =>
        apply DGRightModule.InternalHom.ext
        intro m
        rw [DGRightModule.InternalHom.differential_apply_of_mem _ _
          (curryValue_mem f l.2), curryValue_apply, curryValue_apply, curryValue_apply,
          DGRightModuleCat.map_d f,
          DGRightModuleCat.tensorBimoduleObj_differential_tmul l.2, map_add]
        rw [TauCeti.negOnePow_smul_eq_negOnePowCast_smul (R := R),
          show f (TauCeti.negOnePowCast R p • tmul R A (l : L) (M.differential m)) =
              TauCeti.negOnePowCast R p • f (tmul R A (l : L) (M.differential m)) from
            f.toLinearMap.map_smul_of_tower _ _,
          TauCeti.negOnePow_smul_eq_negOnePowCast_smul (R := R)]
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
  map_smul' b z := by
    induction z using BalancedTensorProduct.induction_on with
    | ht l m =>
        change lift (uncurryBilinear g) (uncurryBilinear_balanced g)
          (b • tmul R A l m) = _
        rw [BalancedTensorProduct.smul_tmul_right,
          lift_tmul, lift_tmul, uncurryBilinear_apply, uncurryBilinear_apply]
        exact map_smul (g l) b m
    | ha x y hx hy => simp only [smul_add, map_add, hx, hy]

@[simp]
private theorem uncurryLinearMap_tmul (g : L ⟶ M.internalHomObj N) (l : L) (m : M) :
    uncurryLinearMap g (tmul R A l m) = g l m := by
  change lift (uncurryBilinear g) (uncurryBilinear_balanced g) (tmul R A l m) = _
  rw [lift_tmul, uncurryBilinear_apply]

private abbrev uncurryBaseLinearMap (g : L ⟶ M.internalHomObj N) :
    DGRightModuleCat.tensorBimoduleObj L M →ₗ[R] N where
  toFun := uncurryLinearMap g
  map_add' := map_add _
  map_smul' r z := (uncurryLinearMap g).map_smul_of_tower r z

private theorem uncurryBaseLinearMap_apply (g : L ⟶ M.internalHomObj N)
    (z : DGRightModuleCat.tensorBimoduleObj L M) :
    uncurryBaseLinearMap g z = uncurryLinearMap g z := (rfl)

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
      (uncurryBaseLinearMap g) 0
      (fun {q r} {l m} hl hm ↦ by
        have hl' : l ∈ L.grading q := by
          simpa only [InternalGrading.ofDecomposition_piece] using hl
        have hm' : m ∈ M.grading r := by
          simpa only [InternalGrading.ofDecomposition_piece] using hm
        have hg := DGRightModule.InternalHom.map_mem_of_mem_grading
          (Graded.map_mem g hl') hm'
        rw [uncurryBaseLinearMap_apply, uncurryLinearMap_tmul]
        simpa only [add_zero, add_comm r q] using hg)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hz)
    rw [uncurryBaseLinearMap_apply] at h
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
            rw [TauCeti.negOnePow_smul_eq_negOnePowCast_smul (R := R)] at h
            rw [uncurryLinearMap_tmul, DGRightModuleCat.tensorBimoduleObj_differential_tmul l.2,
              map_add, uncurryLinearMap_tmul,
              TauCeti.negOnePow_smul_eq_negOnePowCast_smul (R := R),
              (uncurryLinearMap g).map_smul_of_tower, uncurryLinearMap_tmul]
            exact eq_add_of_sub_eq h
        | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | ha x y hx hy => simp only [map_add, hx, hy]

@[simp]
private theorem uncurry_tmul (g : L ⟶ M.internalHomObj N) (l : L) (m : M) :
    uncurry g (tmul R A l m) = g l m := by
  change (uncurry g).toLinearMap (tmul R A l m) = _
  rw [show (uncurry g).toLinearMap = uncurryLinearMap g from rfl]
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
def tensorInternalHomAdjunction : M.tensorRightModule ⊣ M.internalHom :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv (M := M)
      homEquiv_naturality_left_symm := fun f g ↦ by
        apply DGRightModuleCat.tensorBimoduleObj_hom_ext
        intro l m
        rw [DGRightModuleCat.comp_apply, DGRightModuleCat.tensorBimoduleMap_tmul,
          DGBimoduleCat.id_apply, tensorHomEquiv_symm_apply_tmul,
          tensorHomEquiv_symm_apply_tmul,
          DGRightModuleCat.comp_apply]
      homEquiv_naturality_right := tensorHomEquiv_naturality_right (M := M) }

end TauCeti.DGBimoduleCat
