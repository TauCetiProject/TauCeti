/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BasepointChange

/-!
# Changing the basepoint along the paths from a point to itself

A DG local system at a point `a` of a space `B` is a right DG module `M` over the chain algebra
`C_*(Ω_a B)` of Moore loops, and tensoring with the chain bimodule `C_*(P_{a→b} B)` of Moore paths
from `a` to `b` changes its basepoint to `b`. This file shows that for `b = a` the change of
basepoint is isomorphic to the identity, as a functor of DG local systems at `a`
(`TauCeti.tensorPathChainOneNatIso`).

The isomorphism `M ⊗ C_*(P_{a→a} B) ≅ M` is `m ⊗ c ↦ m · ρ(c)`, where `ρ` reads a chain of paths
from `a` to itself as a chain of loops at `a`. This is the map `TauCeti.tensorPathChainAct` of
the general change of basepoint for the constant path of length zero, along which appending the
reversed path changes nothing. Since Moore concatenation is strictly unital, `ρ` is then linear for
the loops at `a` acting on both sides (`TauCeti.pathChainToLoopChain_one_op_smul`), so the map is
a morphism of DG local systems at `a`, and it is inverse to `m ↦ m ⊗ [1]`, tensoring with the
`0`-chain of the constant path. For a general path `δ` from `a` to `b`, the source
`M ⊗ C_*(P_{a→b} B)` is a module over `C_*(Ω_b B)` while `M` is a module over `C_*(Ω_a B)`, so
the map `m ⊗ c ↦ m · ρ_δ(c)` is only `R`-linear: it is the inclusion of the homotopy retract
`M ⊗ C_*(P_{a→b} B)` into `M`, with `m ↦ m ⊗ [δ]` as the retraction back.

This is the unit law for changes of basepoint. Composing the change along the paths from `a` to
`b` with the change along the paths from `b` back to `a` is quasi-isomorphic to the change along
the paths from `a` to itself, and this file identifies the latter with the identity.

## Main definitions

* `TauCeti.tensorPathChainOneIso`: `M ⊗ C_*(P_{a→a} B) ≅ M`, as DG local systems at `a`.
* `TauCeti.tensorPathChainOneNatIso`: the change of basepoint along the paths from `a` to itself
  is naturally isomorphic to the identity functor.

## Main results

* `TauCeti.pathChainToLoopChain_one_op_smul`: for the constant path, `ρ` is linear for the right
  action of the loops at `a`.
* `TauCeti.pathChainToLoopChain_one_smul_pathChainPoint`: acting on the `0`-chain of the constant
  path inverts `ρ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe u w v

variable {B : Type u} [TopologicalSpace B] {a : B} {R : Type w} [CommRing R]

/-- For the constant path of length zero, `ρ` is the push-forward along the identification of
paths from `a` to itself with loops at `a`. -/
theorem pathChainToLoopChain_one_lof {n : ℕ}
    (c : NormalizedCubicalChain (MoorePathBetween B a a) R n) :
    pathChainToLoopChain R (MoorePathBetween.loopHomeomorph a 1)
        (cubicalChainModuleLof _ (MooreLoopSpace B a) R n c) =
      cubicalChainLof (MooreLoopSpace B a) R n
        (NormalizedCubicalChain.map R (MoorePathBetween.loopHomeomorph a).symm n c) := by
  have h :
      (MoorePathBetween.loopAppendHomotopyEquiv (MoorePathBetween.loopHomeomorph a 1)).symm.toFun =
        ((MoorePathBetween.loopHomeomorph a).symm :
          C(MoorePathBetween B a a, MooreLoopSpace B a)) :=
    ContinuousMap.ext fun δ ↦
      MoorePathBetween.loopAppendHomotopyEquiv_loopHomeomorph_one_symm_apply δ
  rw [pathChainToLoopChain_lof, h]

/-- For the constant path of length zero, `ρ : C_*(P_{a→a} B) → C_*(Ω_a B)` is linear for the
loops at `a` acting behind. -/
theorem pathChainToLoopChain_one_op_smul (α : loopChainAlgebra B a R)
    (x : cubicalChainModule (MoorePathBetween B a a) (MooreLoopSpace B a) R) :
    pathChainToLoopChain R (MoorePathBetween.loopHomeomorph a 1) (op α • x) =
      pathChainToLoopChain R (MoorePathBetween.loopHomeomorph a 1) x * α := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, add_mul]
  | lof q c =>
    induction α using DirectSum.induction_on with
    | zero => simp
    | add α α' hα hα' => rw [MulOpposite.op_add, add_smul, map_add, hα, hα', mul_add]
    | of p y =>
      rw [← DirectSum.lof_eq_of R, op_lof_smul_cubicalChainModuleLof, pathChainToLoopChain_one_lof,
        pathChainToLoopChain_one_lof, cubicalChainLof_mul, NormalizedCubicalChain.map_act _
          (fun ω γ ↦ MoorePathBetween.loopHomeomorph_symm_op_smul γ ω),
        NormalizedCubicalChain.act_eq_mul]

/-- `ρ` sends the `0`-chain of the constant path of length zero to the unit of `C_*(Ω_a B)`. -/
@[simp]
theorem pathChainToLoopChain_one_pathChainPoint :
    pathChainToLoopChain R (MoorePathBetween.loopHomeomorph a 1)
        (pathChainPoint R (MoorePathBetween.loopHomeomorph a 1)) = 1 := by
  have h :
      ((MoorePathBetween.loopHomeomorph a).symm :
          C(MoorePathBetween B a a, MooreLoopSpace B a)).comp
        (SingularCube.point (MoorePathBetween.loopHomeomorph a 1)) = SingularCube.point 1 :=
    ContinuousMap.ext fun _ ↦ by simp [SingularCube.point_apply]
  rw [pathChainPoint_def, pathChainToLoopChain_one_lof, NormalizedCubicalChain.map_ofCube, h,
    ← NormalizedCubicalChain.one_def, cubicalChainLof_one]

/-- Acting on the `0`-chain of the constant path of length zero inverts `ρ`: the chain of loops
`ρ(x)` acts on it by concatenation in front, which recovers `x`. -/
@[simp]
theorem pathChainToLoopChain_one_smul_pathChainPoint
    (x : cubicalChainModule (MoorePathBetween B a a) (MooreLoopSpace B a) R) :
    pathChainToLoopChain R (MoorePathBetween.loopHomeomorph a 1) x •
        pathChainPoint R (MoorePathBetween.loopHomeomorph a 1) = x := by
  have h : (MoorePathBetween.append (MoorePathBetween.loopHomeomorph a 1) a).comp
      (MoorePathBetween.append (MoorePathBetween.loopHomeomorph a 1).symm a) =
        ContinuousMap.id _ :=
    ContinuousMap.ext fun γ ↦ MoorePathBetween.ext (by simp)
  rw [pathChainToLoopChain_smul_pathChainPoint, h, cubicalChainModuleLinearMap_id,
    LinearMap.id_apply]

section Iso

open BalancedTensorProduct DGRightModuleCat

/-- The right action of the loop chains on `M ⊗ C_*(P_{a→a} B)`, which instance search does not
see through the carrier of the tensor product. -/
local instance (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)) :
    Module (loopChainAlgebra B a R)ᵐᵒᵖ (tensorBimoduleObj M (pathChainBimodule B a a R)) :=
  (tensorBimoduleObj M (pathChainBimodule B a a R)).moduleOp

variable (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))

/-- Tensoring with the `0`-chain of the constant path of length zero is a right inverse of
`m ⊗ c ↦ m · ρ(c)`. -/
theorem tensorPathChainAct_one_tensorPathChainPoint (m : M) :
    tensorPathChainAct M (MoorePathBetween.loopHomeomorph a 1)
        (tensorPathChainPoint M (MoorePathBetween.loopHomeomorph a 1) m) = m := by
  rw [tensorPathChainPoint_apply, tensorPathChainAct_tmul,
    pathChainToLoopChain_one_pathChainPoint, op_one, one_smul]

/-- Tensoring with the `0`-chain of the constant path of length zero is a left inverse of
`m ⊗ c ↦ m · ρ(c)`. -/
theorem tensorPathChainPoint_one_tensorPathChainAct
    (z : tensorBimoduleObj M (pathChainBimodule B a a R)) :
    tensorPathChainPoint M (MoorePathBetween.loopHomeomorph a 1)
        (tensorPathChainAct M (MoorePathBetween.loopHomeomorph a 1) z) = z := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => rw [map_add, map_add, hz, hz']
  | ht m c =>
    rw [tensorPathChainAct_tmul, tensorPathChainPoint_apply, balance,
      pathChainToLoopChain_one_smul_pathChainPoint]

/-- For the constant path of length zero, `m ⊗ c ↦ m · ρ(c)` is linear for the loops at `a`
acting behind. -/
theorem tensorPathChainAct_one_op_smul (α : loopChainAlgebra B a R)
    (z : tensorBimoduleObj M (pathChainBimodule B a a R)) :
    tensorPathChainAct M (MoorePathBetween.loopHomeomorph a 1) (op α • z) =
      op α • tensorPathChainAct M (MoorePathBetween.loopHomeomorph a 1) z := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
  | ht m c =>
    rw [smul_tmul_right, tensorPathChainAct_tmul, tensorPathChainAct_tmul,
      pathChainToLoopChain_one_op_smul, op_mul, mul_smul]

variable (B a R)

/-- **Changing the basepoint along the paths from a point to itself does nothing**: for a DG local
system `M` at `a`, the map `m ⊗ c ↦ m · ρ(c)` is an isomorphism `M ⊗ C_*(P_{a→a} B) ≅ M` of DG
local systems at `a`, with inverse `m ↦ m ⊗ [1]`. Here `ρ` reads a chain of paths from `a` to
itself as a chain of loops at `a`. -/
def tensorPathChainOneIso
    (M : DGRightModuleCat.{w, max u w, max u w v} (loopChain_isDGAlgebra B a R)) :
    tensorBimoduleObj M (pathChainBimodule B a a R) ≅ M :=
  isoMk
    { toFun := tensorPathChainAct M (MoorePathBetween.loopHomeomorph a 1)
      invFun := tensorPathChainPoint M (MoorePathBetween.loopHomeomorph a 1)
      map_add' := map_add _
      map_smul' := fun α z ↦ by
        rw [← op_unop α]
        exact tensorPathChainAct_one_op_smul M _ z
      left_inv := tensorPathChainPoint_one_tensorPathChainAct M
      right_inv := tensorPathChainAct_one_tensorPathChainPoint M }
    (fun q z ↦ ⟨tensorPathChainAct_mem _, fun hz ↦ by
      rw [← tensorPathChainPoint_one_tensorPathChainAct M z]
      exact tensorPathChainPoint_mem _ hz⟩)
    (fun z ↦ differential_tensorPathChainAct _ z)

variable {B a R}

/-- The isomorphism `M ⊗ C_*(P_{a→a} B) ≅ M` is the map `TauCeti.tensorPathChainAct` for the
constant path of length zero. -/
theorem tensorPathChainOneIso_hom_apply
    (M : DGRightModuleCat.{w, max u w, max u w v} (loopChain_isDGAlgebra B a R))
    (z : tensorBimoduleObj M (pathChainBimodule B a a R)) :
    (tensorPathChainOneIso.{u, w, v} B a R M).hom z =
      tensorPathChainAct M (MoorePathBetween.loopHomeomorph a 1) z := by
  rw [tensorPathChainOneIso, isoMk_hom_apply, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk]

/-- The isomorphism `M ⊗ C_*(P_{a→a} B) ≅ M` is `m ⊗ c ↦ m · ρ(c)`. -/
@[simp]
theorem tensorPathChainOneIso_hom_tmul
    (M : DGRightModuleCat.{w, max u w, max u w v} (loopChain_isDGAlgebra B a R)) (m : M)
    (c : cubicalChainModule (MoorePathBetween B a a) (MooreLoopSpace B a) R) :
    (tensorPathChainOneIso.{u, w, v} B a R M).hom
        (BalancedTensorProduct.tmul R (loopChainAlgebra B a R) m c) =
      op (pathChainToLoopChain R (MoorePathBetween.loopHomeomorph a 1) c) • m := by
  rw [tensorPathChainOneIso_hom_apply, tensorPathChainAct_tmul]

/-- The inverse of the isomorphism `M ⊗ C_*(P_{a→a} B) ≅ M` is `m ↦ m ⊗ [1]`. -/
@[simp]
theorem tensorPathChainOneIso_inv_apply
    (M : DGRightModuleCat.{w, max u w, max u w v} (loopChain_isDGAlgebra B a R)) (m : M) :
    (tensorPathChainOneIso.{u, w, v} B a R M).inv m =
      BalancedTensorProduct.tmul R (loopChainAlgebra B a R) m
        (pathChainPoint R (MoorePathBetween.loopHomeomorph a 1)) := by
  rw [tensorPathChainOneIso, isoMk_inv_apply, LinearEquiv.coe_symm_mk,
    tensorPathChainPoint_apply]

/-- The isomorphism `M ⊗ C_*(P_{a→a} B) ≅ M` is natural in `M`. -/
@[reassoc]
theorem tensorPathChainOneIso_hom_naturality
    {M N : DGRightModuleCat.{w, max u w, max u w v} (loopChain_isDGAlgebra B a R)} (f : M ⟶ N) :
    tensorBimoduleMap f (𝟙 (pathChainBimodule B a a R)) ≫
        (tensorPathChainOneIso.{u, w, v} B a R N).hom =
      (tensorPathChainOneIso.{u, w, v} B a R M).hom ≫ f := by
  ext z
  rw [DGRightModuleCat.comp_apply, DGRightModuleCat.comp_apply, tensorPathChainOneIso_hom_apply,
    tensorPathChainOneIso_hom_apply]
  exact tensorPathChainAct_tensorBimoduleMap _ f z

variable (B a R)

/-- **Changing the basepoint along the paths from a point to itself is naturally isomorphic to the
identity**: the functor `M ↦ M ⊗ C_*(P_{a→a} B)` on DG local systems at `a` is isomorphic to the
identity functor, through `m ⊗ c ↦ m · ρ(c)`. -/
def tensorPathChainOneNatIso :
    tensorBimoduleFunctor.flip.obj (pathChainBimodule B a a R) ≅
      𝟭 (DGRightModuleCat.{w, max u w, max u w v} (loopChain_isDGAlgebra B a R)) :=
  NatIso.ofComponents (tensorPathChainOneIso.{u, w, v} B a R) fun f ↦
    tensorPathChainOneIso_hom_naturality f

/-- The components of `tensorPathChainOneNatIso` are `tensorPathChainOneIso`. -/
@[simp]
theorem tensorPathChainOneNatIso_app
    (M : DGRightModuleCat.{w, max u w, max u w v} (loopChain_isDGAlgebra B a R)) :
    (tensorPathChainOneNatIso.{u, w, v} B a R).app M = tensorPathChainOneIso.{u, w, v} B a R M :=
      (rfl)

end Iso

end TauCeti
