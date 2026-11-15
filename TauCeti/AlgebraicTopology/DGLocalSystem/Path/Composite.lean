/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BasepointChange
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Concatenation

/-!
# Composing changes of basepoint

For points `a`, `b` and `c` of a space `B`, a DG local system `M` at `a`, that is a right DG module
over `C_*(Ω_a B)`, can be moved to `c` in two steps, tensoring with the chain bimodule
`C_*(P_{a→b} B)` of Moore paths from `a` to `b` and then with `C_*(P_{b→c} B)`, or in one step,
tensoring with `C_*(P_{a→c} B)`. Reassociating and concatenating Moore paths gives a morphism of
DG local systems at `c`, natural in `M`,

`(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→c} B) ⟶ M ⊗ C_*(P_{a→c} B)`

(`TauCeti.tensorPathChainConcat`). It is a quasi-isomorphism as soon as `a` and `b` are joined by
a Moore path (`TauCeti.isQuasiIso_tensorPathChainConcat`): the composite of two changes of
basepoint is the change along the composite. For `c = a` the target is `M ⊗ C_*(P_{a→a} B)`,
which is a homotopy retract of `M` over the ground ring
(`TauCeti.tensorPathChainPoint_tensorPathChainAct`). Showing that the paths from `b` back to `a`
undo the change of basepoint along the paths from `a` to `b` still needs a quasi-isomorphism
`M ⊗ C_*(P_{a→a} B) ⟶ M` of DG local systems at `a`, which this file does not construct.

Fix Moore paths `δ` from `a` to `b` and `δ'` from `b` to `c`. Both sides are homotopy retracts of
`M` through the maps `m ⊗ x ↦ m · ρ(x)` appending the reversal of a path: the source through `δ'`
and then `δ`, the target through `δ ⋆ δ'`. Since the reversal of `δ ⋆ δ'` is `δ'⁻¹ ⋆ δ⁻¹`, the
composition commutes with these retractions, and so it is a quasi-isomorphism
(`TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyRetract`).

## Main definitions

* `TauCeti.tensorPathChainConcat M b c`: the composition of the changes of basepoint of `M` along
  the paths from `a` to `b` and from `b` to `c`, compared with the change along the paths from `a`
  to `c`.

## Main results

* `TauCeti.tensorPathChainConcat_tmul`: on pure tensors, `(m ⊗ x) ⊗ y ↦ m ⊗ (x ⋆ y)`.
* `TauCeti.tensorPathChainConcat_naturality`: the composition is natural in `M`.
* `TauCeti.pathChainToLoopChain_trans_pathChainConcat`: appending the reversal of `δ ⋆ δ'` to a
  concatenation `x ⋆ y` is appending the reversal of `δ` to `x` acted on by `y ⋆ δ'⁻¹`.
* `TauCeti.isQuasiIso_tensorPathChainConcat`: the composite of two changes of basepoint is
  quasi-isomorphic to the change along the composite paths.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

open BalancedTensorProduct DGRightModuleCat

universe u w v

variable {B : Type u} [TopologicalSpace B] {R : Type w} [CommRing R] {a b c : B}

/-- Appending the reversal of `δ ⋆ δ'` to a concatenation `x ⋆ y` is appending the reversal of
`δ` to `x`, acted on by the loops `y ⋆ δ'⁻¹` at `b`. -/
theorem pathChainToLoopChain_trans_pathChainConcat (δ : MoorePathBetween B a b)
    (δ' : MoorePathBetween B b c)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (y : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainToLoopChain R (δ.trans δ')
        (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) x y)) =
      pathChainToLoopChain R δ (op (pathChainToLoopChain R δ' y) • x) := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [add_tmul, map_add, map_add, hx, hx', smul_add, map_add]
  | lof p σ =>
    induction y using cubicalChainModule.induction_on with
    | add y y' hy hy' =>
      rw [tmul_add, map_add, map_add, hy, hy', map_add, MulOpposite.op_add, add_smul, map_add]
    | lof q τ =>
      rw [pathChainConcat_tmul, cubicalChainPairing_lof_lof, pathChainToLoopChain_lof,
        pathChainToLoopChain_lof, op_lof_smul_cubicalChainModuleLof, pathChainToLoopChain_lof,
        NormalizedCubicalChain.act_def]
      have h : NormalizedCubicalChain.crossProduct _ _ R p q σ
          (NormalizedCubicalChain.map R δ'.loopAppendHomotopyEquiv.symm.toFun q τ) =
          NormalizedCubicalChain.map R
            ((ContinuousMap.id _).prodMap δ'.loopAppendHomotopyEquiv.symm.toFun) (p + q)
            (NormalizedCubicalChain.crossProduct _ _ R p q σ τ) := by
        rw [NormalizedCubicalChain.map_crossProduct, NormalizedCubicalChain.map_id,
          LinearMap.id_apply]
      simp only [h, NormalizedCubicalChain.map_map]
      refine congrArg (fun F ↦ cubicalChainLof (MooreLoopSpace B a) R (p + q)
        (NormalizedCubicalChain.map R F (p + q) _)) (ContinuousMap.ext fun ⟨x, y⟩ ↦ ?_)
      exact MooreLoopSpace.ext (by simp [MoorePath.trans_assoc])

/-- Concatenating the `0`-chains of `δ` and `δ'` gives the `0`-chain of `δ ⋆ δ'`. -/
@[simp]
theorem pathChainConcat_tmul_pathChainPoint (δ : MoorePathBetween B a b)
    (δ' : MoorePathBetween B b c) :
    pathChainConcat B a b c R
        (tmul R (loopChainAlgebra B b R) (pathChainPoint R δ) (pathChainPoint R δ')) =
      pathChainPoint R (δ.trans δ') := by
  rw [pathChainPoint_def, pathChainPoint_def, pathChainConcat_tmul,
    cubicalChainPairing_lof_point_left, cubicalChainModuleLinearMap_lof,
    NormalizedCubicalChain.map_ofCube, pathChainPoint_def]
  exact congrArg (fun σ ↦ cubicalChainModuleLof _ (MooreLoopSpace B c) R 0
    (NormalizedCubicalChain.ofCube _ R σ)) (ContinuousMap.ext fun _ ↦ by simp)

section Composite

/-- The outer right action on the change of basepoint of a DG local system. Instance search
unfolds the carrier of a tensor product to a balanced tensor product, which carries its outer right
action only as bundled data. -/
local instance (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)) :
    Module (loopChainAlgebra B b R)ᵐᵒᵖ (tensorBimoduleObj M (pathChainBimodule B a b R)) :=
  (tensorBimoduleObj M (pathChainBimodule B a b R)).moduleOp

/-- **Composing changes of basepoint**: the morphism of DG local systems at `c`
`(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→c} B) ⟶ M ⊗ C_*(P_{a→c} B)`, reassociating and then
concatenating Moore paths. -/
def tensorPathChainConcat (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))
    (b c : B) :
    tensorBimoduleObj (tensorBimoduleObj M (pathChainBimodule B a b R))
        (pathChainBimodule B b c R) ⟶
      tensorBimoduleObj M (pathChainBimodule B a c R) :=
  DGBimoduleCat.forgetToRightModuleCat.map
    ((DGBimoduleCat.tensorAssoc M.toScalarBimodule (pathChainBimodule B a b R)
        (pathChainBimodule B b c R)).hom ≫
      DGBimoduleCat.tensorMap (𝟙 M.toScalarBimodule) (pathChainConcat B a b c R))

/-- On pure tensors, `(m ⊗ x) ⊗ y ↦ m ⊗ (x ⋆ y)`. -/
@[simp]
theorem tensorPathChainConcat_tmul
    (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)) (m : M)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (y : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    tensorPathChainConcat M b c
        (tmul R (loopChainAlgebra B b R) (tmul R (loopChainAlgebra B a R) m x) y) =
      tmul R (loopChainAlgebra B a R) m
        (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) x y)) := by
  -- The forgetful functor keeps the underlying map of a bimodule morphism.
  refine (DGBimoduleCat.comp_apply _ _ _).trans ?_
  rw [DGBimoduleCat.tensorAssoc_hom_tmul, DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.id_apply]

/-- **Composing changes of basepoint is natural** in the DG local system. -/
theorem tensorPathChainConcat_naturality
    {M N : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)} (f : M ⟶ N) :
    tensorBimoduleMap (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R)))
          (𝟙 (pathChainBimodule B b c R)) ≫ tensorPathChainConcat N b c =
      tensorPathChainConcat M b c ≫ tensorBimoduleMap f (𝟙 (pathChainBimodule B a c R)) := by
  refine tensorBimoduleObj_hom_ext fun w y ↦ ?_
  induction w using BalancedTensorProduct.induction_on with
  | ht m x =>
    rw [DGRightModuleCat.comp_apply, DGRightModuleCat.comp_apply, tensorBimoduleMap_tmul,
      tensorBimoduleMap_tmul, DGBimoduleCat.id_apply, DGBimoduleCat.id_apply,
      tensorPathChainConcat_tmul, tensorPathChainConcat_tmul, tensorBimoduleMap_tmul,
      DGBimoduleCat.id_apply]
  | ha w w' hw hw' => simp only [add_tmul, map_add, hw, hw']

/-- **Acting after composing is acting twice**: following the composite change of basepoint by
`m ⊗ z ↦ m · ρ_{δ ⋆ δ'}(z)` is acting first through `ρ_{δ'}` and then through `ρ_δ`. -/
theorem tensorPathChainAct_tensorPathChainConcat
    (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))
    (δ : MoorePathBetween B a b) (δ' : MoorePathBetween B b c)
    (z : tensorBimoduleObj (tensorBimoduleObj M (pathChainBimodule B a b R))
      (pathChainBimodule B b c R)) :
    tensorPathChainAct M (δ.trans δ') (tensorPathChainConcat M b c z) =
      tensorPathChainAct M δ
        (tensorPathChainAct (tensorBimoduleObj M (pathChainBimodule B a b R)) δ' z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => simp only [map_add, hz, hz']
  | ht w y =>
    induction w using BalancedTensorProduct.induction_on with
    | ha w w' hw hw' => simp only [add_tmul, map_add, hw, hw']
    | ht m x =>
      rw [tensorPathChainConcat_tmul, tensorPathChainAct_tmul, tensorPathChainAct_tmul,
        smul_tmul_right, tensorPathChainAct_tmul, pathChainToLoopChain_trans_pathChainConcat]

/-- **Composing the points is the point of the composite**: tensoring with `[δ]` and then with
`[δ']` and composing the changes of basepoint is tensoring with `[δ ⋆ δ']`. -/
theorem tensorPathChainConcat_tensorPathChainPoint
    (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))
    (δ : MoorePathBetween B a b) (δ' : MoorePathBetween B b c) (m : M) :
    tensorPathChainConcat M b c
        (tensorPathChainPoint (tensorBimoduleObj M (pathChainBimodule B a b R)) δ'
          (tensorPathChainPoint M δ m)) =
      tensorPathChainPoint M (δ.trans δ') m := by
  rw [tensorPathChainPoint_apply, tensorPathChainPoint_apply, tensorPathChainConcat_tmul,
    pathChainConcat_tmul_pathChainPoint, tensorPathChainPoint_apply]

/-- **The composite of two changes of basepoint is the change along the composite**: as soon as
`a` and `b` are joined by a Moore path, the morphism
`(M ⊗ C_*(P_{a→b} B)) ⊗ C_*(P_{b→c} B) ⟶ M ⊗ C_*(P_{a→c} B)` is a quasi-isomorphism. The
hypothesis cannot be dropped: without a path from `a` to `b` the source vanishes, while for
`c = a` the target need not. -/
theorem isQuasiIso_tensorPathChainConcat
    (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))
    (h : Nonempty (MoorePathBetween B a b)) : IsQuasiIso (tensorPathChainConcat M b c) := by
  -- Instance search does not see the structures of a tensor product through its carrier.
  let := (tensorBimoduleObj (tensorBimoduleObj M (pathChainBimodule B a b R))
    (pathChainBimodule B b c R)).moduleOp
  let := (tensorBimoduleObj (tensorBimoduleObj M (pathChainBimodule B a b R))
    (pathChainBimodule B b c R)).scalarTower
  let := (tensorBimoduleObj (tensorBimoduleObj M (pathChainBimodule B a b R))
    (pathChainBimodule B b c R)).gradedSMul
  let := (tensorBimoduleObj M (pathChainBimodule B a c R)).moduleOp
  let := (tensorBimoduleObj M (pathChainBimodule B a c R)).scalarTower
  let := (tensorBimoduleObj M (pathChainBimodule B a c R)).gradedSMul
  obtain ⟨δ⟩ := h
  rcases isEmpty_or_nonempty (MoorePathBetween B b c) with hc | hc
  · -- Without Moore paths from `b` to `c` there are none from `a` to `c` either, so both sides
    -- vanish.
    have : IsEmpty (MoorePathBetween B a c) := ⟨fun γ ↦ isEmptyElim (δ.symm.trans γ)⟩
    exact DGRightModuleHom.isQuasiIso_of_subsingleton _
  · obtain ⟨δ'⟩ := hc
    -- Both sides are homotopy retracts of `M`: the source through `ρ_{δ'}` and then `ρ_δ`, the
    -- target through `ρ_{δ ⋆ δ'}`, and the composite of changes commutes with these retractions.
    let N := tensorBimoduleObj M (pathChainBimodule B a b R)
    refine DGRightModuleHom.isQuasiIso_of_homotopyRetract (tensorPathChainConcat M b c)
      (LinearMap.id : M →ₗ[R] M)
      (fun x y _ hxy ↦ ⟨y, 0, hxy.symm, by rw [map_zero, add_zero, LinearMap.id_apply]⟩)
      (tensorPathChainAct M δ ∘ₗ tensorPathChainAct N δ')
      (tensorPathChainPoint N δ' ∘ₗ tensorPathChainPoint M δ)
      (tensorPathChainHomotopy N δ' +
        tensorPathChainPoint N δ' ∘ₗ tensorPathChainHomotopy M δ ∘ₗ tensorPathChainAct N δ')
      (tensorPathChainAct M (δ.trans δ')) (tensorPathChainPoint M (δ.trans δ'))
      (tensorPathChainHomotopy M (δ.trans δ')) (fun z ↦ ?_) (fun m ↦ ?_)
      (differential_tensorPathChainAct _) (differential_tensorPathChainPoint _) (fun z ↦ ?_)
      (tensorPathChainPoint_tensorPathChainAct _)
      (tensorPathChainAct_tensorPathChainConcat M δ δ')
      (tensorPathChainConcat_tensorPathChainPoint M δ δ')
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, differential_tensorPathChainAct,
        differential_tensorPathChainAct]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, differential_tensorPathChainPoint,
        differential_tensorPathChainPoint]
    · -- The homotopy of a composite of homotopy retracts.
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [tensorPathChainPoint_tensorPathChainAct, map_add, map_add,
        tensorPathChainPoint_tensorPathChainAct, ← differential_tensorPathChainPoint,
        differential_tensorPathChainAct]
      simp only [map_add]
      abel

end Composite

end TauCeti
