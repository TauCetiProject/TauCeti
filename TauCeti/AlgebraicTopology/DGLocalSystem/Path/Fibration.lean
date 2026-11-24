/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Fibration
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.CompositeChange
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Prism
public import TauCeti.Topology.PathSpace.Moore.Replacement.Append

/-!
# Changing the basepoint of the DG local system of a map

For a continuous map `p : E → B` and a point `a ∈ B`, the DG local system of `p` at `a` is the
chain module `C_*(F'_a)` of the fibre of the Moore-path replacement of `p` over `a`, a right DG
module over `C_*(Ω_a B)` (`TauCeti.fibrationLocalSystem`). Its basepoint change to `b` is
`C_*(F'_a) ⊗_{C_*(Ω_a B)} C_*(P_{a→b} B)` (`TauCeti.DGLocalSystem.basepointChange`). This file
compares it with the DG local system of `p` at `b`: appending Moore paths to the points of the
fibre, `((e, γ), δ) ↦ (e, γ ⋆ δ)`, is balanced over the loops at `a` and commutes with the loops
at `b`, so it induces a morphism of DG local systems at `b`
(`TauCeti.fibrationLocalSystemAppend`)

`C_*(F'_a) ⊗_{C_*(Ω_a B)} C_*(P_{a→b} B) ⟶ C_*(F'_b)`, `m ⊗ σ ↦ append_*(m × σ)`.

It is a quasi-isomorphism as soon as `a` and `b` are joined by a Moore path
(`TauCeti.isQuasiIso_fibrationLocalSystemAppend`), for every map `p`: no fibration hypothesis is
needed, because the replacement is always a fibration. So the DG local system of a map is
independent of the basepoint within a path component, through a specified quasi-isomorphism.
The morphism is natural in maps over `B` (`TauCeti.fibrationLocalSystemAppend_naturality`) and
compatible with the composite change of basepoint
(`TauCeti.tensorPathChainConcat_fibrationLocalSystemAppend`).

The proof shows that source and target are both homotopy retracts of `C_*(F'_a)`, compatibly
with the morphism. For a Moore path `δ` from `a` to `b`, the source is a homotopy retract through
`m ⊗ σ ↦ m · ρ_δ(σ)` and `m ↦ m ⊗ [δ]` (`TauCeti.tensorPathChainPoint_tensorPathChainAct`).
The target is one through appending `δ⁻¹` and appending `δ`, whose composite is homotopic to the
identity of `F'_b` (`TauCeti.MooreReplacement.Fiber.appendSymmHomotopy`). The morphism sends
`m ⊗ [δ]` to the push-forward of `m` along appending `δ`, and following it by appending `δ⁻¹`
gives `m · ρ_δ(σ)` on `m ⊗ σ`, by strict associativity of Moore concatenation. A morphism
compatible in this way with two homotopy retractions onto the same module is a quasi-isomorphism
(`TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyRetract`).

## Main definitions

* `TauCeti.fibrationLocalSystemAppend R p a b`: the morphism
  `C_*(F'_a) ⊗_{C_*(Ω_a B)} C_*(P_{a→b} B) ⟶ C_*(F'_b)` of DG local systems at `b`.

## Main results

* `TauCeti.fibrationLocalSystemAppend_tmul`: on pure tensors it is the pairing of chains induced
  by appending paths.
* `TauCeti.fibrationLocalSystemAppend_tmul_pathChainPoint`: on `m ⊗ [δ]` it pushes `m` forward
  along appending `δ`.
* `TauCeti.isQuasiIso_fibrationLocalSystemAppend`: if `a` and `b` are joined by a Moore path, it
  is a quasi-isomorphism.
* `TauCeti.fibrationLocalSystemAppend_naturality`: it is natural in maps over `B`.
* `TauCeti.tensorPathChainConcat_fibrationLocalSystemAppend`: changing the basepoint from `a` to
  `b` and then to `c` agrees with changing it from `a` to `c`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
-/

public noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

open BalancedTensorProduct DGRightModuleCat MooreReplacement

universe u w

variable {E E' B : Type u} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {R : Type w} [CommRing R]

section Append

variable (R) (p : C(E, B)) (a b : B)

/-- **Changing the basepoint of the DG local system of a map**: the morphism of DG local systems
at `b`

`C_*(F'_a) ⊗_{C_*(Ω_a B)} C_*(P_{a→b} B) ⟶ C_*(F'_b)`, `m ⊗ σ ↦ append_*(m × σ)`,

from the basepoint change of the DG local system of `p` at `a` to the DG local system of `p` at
`b`, induced by appending Moore paths to the points of the fibre of the Moore-path replacement. -/
def fibrationLocalSystemAppend :
    tensorBimoduleObj (fibrationLocalSystem R p a) (pathChainBimodule B a b R) ⟶
      fibrationLocalSystem R p b :=
  (DGBimoduleCat.tensorLift (M := (fibrationLocalSystem R p a).toScalarBimodule)
    (N := pathChainBimodule B a b R) (P := (fibrationLocalSystem R p b).toScalarBimodule)
    (cubicalChainPairing (MooreLoopSpace B a) (MooreLoopSpace B b) R (Fiber.appendMap p a b))
    (cubicalChainPairing_op_smul_left _ fun ω x δ ↦ by
      rw [Fiber.appendMap_apply, Fiber.appendMap_apply, Fiber.op_smul_eq_act]
      exact Fiber.act_append x ω δ)
    (fun r m c ↦ LinearMap.map_smul₂ _ r m c)
    (cubicalChainPairing_op_smul_right _ fun ω x δ ↦ by
      rw [Fiber.appendMap_apply, Fiber.appendMap_apply, Fiber.op_smul_eq_act]
      exact Fiber.append_op_smul x δ ω)
    (fun hm hc ↦ cubicalChainPairing_mem _ hm hc)
    (fun hm c ↦ cubicalChainModuleDifferential_cubicalChainPairing _ hm c)).val

variable {R p a b}

/-- On pure tensors, the change of basepoint is the pairing of chains induced by appending paths
to the points of the fibre. -/
@[simp]
theorem fibrationLocalSystemAppend_tmul (m : fibrationLocalSystem R p a)
    (c : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    fibrationLocalSystemAppend R p a b (tmul R (loopChainAlgebra B a R) m c) =
      cubicalChainPairing (MooreLoopSpace B a) (MooreLoopSpace B b) R (Fiber.appendMap p a b)
        m c := by
  rw [fibrationLocalSystemAppend]
  exact DGBimoduleCat.tensorLift_tmul (M := (fibrationLocalSystem R p a).toScalarBimodule)
    (N := pathChainBimodule B a b R) _ _ _ _ (fun hm hc ↦ cubicalChainPairing_mem _ hm hc) _ m c

/-- On `m ⊗ [δ]`, the change of basepoint pushes `m` forward along appending `δ`. -/
theorem fibrationLocalSystemAppend_tmul_pathChainPoint (m : fibrationLocalSystem R p a)
    (δ : MoorePathBetween B a b) :
    fibrationLocalSystemAppend R p a b (tmul R (loopChainAlgebra B a R) m (pathChainPoint R δ)) =
      cubicalChainModuleLinearMap R (Fiber.appendPath δ) m := by
  rw [fibrationLocalSystemAppend_tmul, pathChainPoint_def, cubicalChainPairing_lof_point_right]
  exact congrArg (fun F ↦ cubicalChainModuleLinearMap R F m) (ContinuousMap.ext fun _ ↦ by simp)

/-- Following the change of basepoint by appending `δ⁻¹` is the map `m ⊗ σ ↦ m · ρ_δ(σ)`, where
`ρ_δ` appends `δ⁻¹`: on paths, both send `((e, γ), σ)` to `(e, γ ⋆ σ ⋆ δ⁻¹)`. -/
theorem cubicalChainModuleLinearMap_appendPath_symm_fibrationLocalSystemAppend
    (δ : MoorePathBetween B a b)
    (z : tensorBimoduleObj (fibrationLocalSystem R p a) (pathChainBimodule B a b R)) :
    cubicalChainModuleLinearMap R (Fiber.appendPath δ.symm) (fibrationLocalSystemAppend R p a b z) =
      tensorPathChainAct (fibrationLocalSystem R p a) δ z := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => rw [map_add, map_add, hz, hz', map_add]
  | ht m c =>
    -- Read in the direct sums, both sides are pairings of `m` and `c`; compare the maps.
    apply (cubicalChainModuleEquiv (Fiber p a) (MooreLoopSpace B a) R).injective
    rw [fibrationLocalSystemAppend_tmul, tensorPathChainAct_tmul, cubicalChainModuleEquiv_op_smul,
      pathChainToLoopChain_apply,
      cubicalChainModuleEquiv_linearMap, cubicalChainModuleEquiv_cubicalChainPairing,
      cubicalChainSumMap_cubicalChainSumPairing_of_comp (h := ContinuousMap.id _)
        (h' := (MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun)
        (f' := actMap (Fiber p a) (MooreLoopSpace B a)),
      cubicalChainSumMap_id, LinearMap.id_apply]
    intro x σ
    refine Fiber.ext (MooreReplacement.ext (by simp) ?_)
    simp [MoorePath.trans_assoc]

variable (R p a b) in
/-- **Changing the basepoint of the DG local system of a map is a quasi-isomorphism**: if `a` and
`b` are joined by a Moore path, the morphism
`C_*(F'_a) ⊗_{C_*(Ω_a B)} C_*(P_{a→b} B) ⟶ C_*(F'_b)` induced by appending paths is a
quasi-isomorphism of DG local systems at `b`, for every map `p : E → B`. The hypothesis cannot be
dropped: without a path from `a` to `b` the source vanishes, while the target need not. -/
theorem isQuasiIso_fibrationLocalSystemAppend (h : Nonempty (MoorePathBetween B a b)) :
    IsQuasiIso (fibrationLocalSystemAppend R p a b) := by
  obtain ⟨δ⟩ := h
  let M := fibrationLocalSystem R p a
  -- Instance search does not see the graded actions on a tensor product through its carrier.
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).moduleOp
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).scalarTower
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).gradedSMul
  -- Both sides are homotopy retracts of `C_*(F'_a)`: the source through `m ⊗ σ ↦ m · ρ_δ(σ)`
  -- and `m ↦ m ⊗ [δ]`, the target through appending `δ⁻¹` and appending `δ`.
  refine DGRightModuleHom.isQuasiIso_of_homotopyRetract (fibrationLocalSystemAppend R p a b)
    (LinearMap.id : M →ₗ[R] M) (dM₀ := M.differential) (dN₀ := M.differential)
    (fun x y _ hxy ↦ ⟨y, 0, hxy.symm, by rw [map_zero, add_zero, LinearMap.id_apply]⟩)
    (tensorPathChainAct M δ) (tensorPathChainPoint M δ) (tensorPathChainHomotopy M δ)
    (cubicalChainModuleLinearMap R (Fiber.appendPath δ.symm))
    (cubicalChainModuleLinearMap R (Fiber.appendPath δ))
    (cubicalChainModulePrism R (Fiber.appendSymmHomotopy δ))
    (differential_tensorPathChainAct δ) (differential_tensorPathChainPoint δ)
    (fun y ↦ cubicalChainModuleDifferential_linearMap _ y)
    (fun y ↦ cubicalChainModuleDifferential_linearMap _ y)
    (tensorPathChainPoint_tensorPathChainAct δ) (fun y ↦ ?_)
    (cubicalChainModuleLinearMap_appendPath_symm_fibrationLocalSystemAppend δ)
    (fun m ↦ ?_)
  · -- Appending `δ⁻¹` and then `δ` is homotopic to the identity of `F'_b`.
    have h := cubicalChainModuleDifferential_prism_add_prism_differential (G := MooreLoopSpace B b)
      (R := R) (Fiber.appendSymmHomotopy (p := p) δ) y
    rw [cubicalChainModuleLinearMap_comp (G' := MooreLoopSpace B a),
      cubicalChainModuleLinearMap_id, LinearMap.comp_apply, LinearMap.id_apply] at h
    rw [add_assoc, h, add_sub_cancel]
  · rw [tensorPathChainPoint_apply, fibrationLocalSystemAppend_tmul_pathChainPoint,
      LinearMap.id_apply]

end Append

section Naturality

variable {p : C(E, B)} {p' : C(E', B)} {a b c : B}

/-- **The change of basepoint is natural in maps over `B`**: for a map `h : E → E'` over `B`, it
commutes with the morphisms of DG local systems induced by `h` at `a` and at `b`. -/
theorem fibrationLocalSystemAppend_naturality (h : C(E, E')) (hh : p'.comp h = p) :
    tensorBimoduleMap (fibrationLocalSystemMap R (b := a) h hh) (𝟙 (pathChainBimodule B a b R)) ≫
        fibrationLocalSystemAppend R p' a b =
      fibrationLocalSystemAppend R p a b ≫ fibrationLocalSystemMap R h hh := by
  refine tensorBimoduleObj_hom_ext fun m σ ↦ ?_
  rw [DGRightModuleCat.comp_apply, DGRightModuleCat.comp_apply, tensorBimoduleMap_tmul,
    DGBimoduleCat.id_apply, fibrationLocalSystemAppend_tmul, fibrationLocalSystemAppend_tmul,
    fibrationLocalSystemMap_apply, fibrationLocalSystemMap_apply,
    cubicalChainPairing_cubicalChainModuleLinearMap_left,
    cubicalChainModuleLinearMap_cubicalChainPairing]
  exact congrArg (fun F ↦ cubicalChainPairing _ _ R F m σ)
    (ContinuousMap.ext fun q ↦ by simp)

/-- **The change of basepoint is compatible with composite changes of basepoint**: changing the
basepoint of the DG local system of `p` from `a` to `b` and then from `b` to `c` agrees with
changing it from `a` to `c`, through the composite change of basepoint
`(m ⊗ σ) ⊗ τ ↦ m ⊗ (σ ⋆ τ)`. -/
theorem tensorPathChainConcat_fibrationLocalSystemAppend :
    tensorPathChainConcat (fibrationLocalSystem R p a) b c ≫
        fibrationLocalSystemAppend R p a c =
      tensorBimoduleMap (fibrationLocalSystemAppend R p a b) (𝟙 (pathChainBimodule B b c R)) ≫
        fibrationLocalSystemAppend R p b c := by
  refine tensorBimoduleObj_hom_ext fun w τ ↦ ?_
  induction w using BalancedTensorProduct.induction_on with
  | ha w w' hw hw' => simp only [add_tmul, map_add, hw, hw']
  | ht m σ =>
    rw [DGRightModuleCat.comp_apply, DGRightModuleCat.comp_apply, tensorPathChainConcat_tmul,
      tensorBimoduleMap_tmul, DGBimoduleCat.id_apply, fibrationLocalSystemAppend_tmul,
      fibrationLocalSystemAppend_tmul, fibrationLocalSystemAppend_tmul, pathChainConcat_tmul]
    refine (cubicalChainPairing_assoc (fun x δ δ' ↦ ?_) m σ τ).symm
    rw [Fiber.appendMap_apply, Fiber.appendMap_apply, Fiber.appendMap_apply, ContinuousMap.coe_mk]
    exact Fiber.append_append x δ δ'

end Naturality

end TauCeti
