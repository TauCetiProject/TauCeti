/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Concatenation
public import TauCeti.Topology.PathSpace.Moore.Between.Append

/-!
# Appending and closing up paths on chains

Fix a Moore path `γ` from `b` to `c` in a space `B`. On normalized cubical chains of Moore paths
it gives three maps, all linear over the chains on the loops acting in front and commuting with
the boundary:

* appending `γ`, `C_*(P_{a→b} B) → C_*(P_{a→c} B)` (`TauCeti.pathChainAppend`);
* closing up a path from `b` to `c` into a loop at `b` by appending the reversal of `γ`,
  `C_*(P_{b→c} B) → C_*(Ω_b B)` (`TauCeti.pathChainToLoopChain`);
* concatenating with the point chain `[γ]` (`TauCeti.pathChainPoint`), which is appending `γ`
  (`TauCeti.pathChainConcat_tmul_pathChainPoint`).

Neither appending `γ⁻¹` and then `γ`, nor closing up and then acting on `[γ]`, is the identity:
both are the right action of the point chain of the loop `γ⁻¹ ⋆ γ` at `c`
(`TauCeti.loopChainSymmTrans`), a loop of positive duration. That loop is joined to the unit by
the retracing loops of `γ⁻¹`, whose `1`-chain `TauCeti.loopChainRetrace` has boundary
`[γ⁻¹ ⋆ γ] - 1`. So the right action of `[γ⁻¹ ⋆ γ]` is homotopic to the identity on every DG right
module over `C_*(Ω_c B)`, through right multiplication by this `1`-chain. These are the chain-level
inputs for the change of basepoint of DG local systems.

## Main definitions

* `TauCeti.pathChainPoint R γ`: the point chain of a Moore path.
* `TauCeti.pathChainAppend R γ a`: appending `γ` on chains of paths starting at `a`.
* `TauCeti.pathChainToLoopChain R γ`: closing up chains of paths by `γ⁻¹`.
* `TauCeti.loopChainSymmTrans R γ`, `TauCeti.loopChainRetrace R γ`: the point chain of `γ⁻¹ ⋆ γ`
  and a `1`-chain joining it to the unit.

## Main results

* `TauCeti.pathChainAppend_pathChainAppend_symm`,
  `TauCeti.pathChainToLoopChain_smul_pathChainPoint`: both round trips are the right action of
  `[γ⁻¹ ⋆ γ]`.
* `TauCeti.cubicalChainDifferential_loopChainRetrace`: `d (loopChainRetrace R γ) = [γ⁻¹ ⋆ γ] - 1`.
* `TauCeti.op_pathChainToLoopChain_smul`: acting by a closed-up chain is concatenating and then
  appending `γ⁻¹`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public section

noncomputable section

open MulOpposite

namespace TauCeti

open NormalizedCubicalChain BalancedTensorProduct

universe u v

variable {B : Type u} [TopologicalSpace B] {R : Type v} [CommRing R] {a b c : B}

/-! ### Point chains and appending paths -/

variable (R) in
/-- The point chain of a Moore path. -/
def pathChainPoint (γ : MoorePathBetween B b c) :
    cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R :=
  cubicalChainModuleLof _ _ R 0 (ofCube _ R (SingularCube.point γ))

/-- A point chain is a cycle. -/
theorem cubicalChainModuleDifferential_pathChainPoint (γ : MoorePathBetween B b c) :
    cubicalChainModuleDifferential _ _ R (pathChainPoint R γ) = 0 :=
  cubicalChainModuleDifferential_lof_zero _

/-- A point chain has degree zero. -/
theorem pathChainPoint_mem (γ : MoorePathBetween B b c) :
    pathChainPoint R γ ∈ cubicalChainModuleGrading _ (MooreLoopSpace B c) R 0 := by
  simpa [pathChainPoint] using cubicalChainModuleLof_mem (G := MooreLoopSpace B c)
    (ofCube (MoorePathBetween B b c) R (SingularCube.point γ))

variable (R) in
/-- Appending a path `γ` from `b` to `c` to paths from `a` to `b`, on chains. -/
def pathChainAppend (γ : MoorePathBetween B b c) (a : B) :
    cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R →ₗ[R]
      cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R :=
  (cubicalChainModuleEquiv _ _ R).symm.toLinearMap ∘ₗ cubicalChainSumMap R (γ.append a) ∘ₗ
    (cubicalChainModuleEquiv _ _ R).toLinearMap

/-- On a homogeneous chain, appending is the push-forward along concatenation with `γ`. -/
@[simp]
theorem pathChainAppend_lof (γ : MoorePathBetween B b c) (a : B) {n : ℕ}
    (s : NormalizedCubicalChain (MoorePathBetween B a b) R n) :
    pathChainAppend R γ a (cubicalChainModuleLof _ _ R n s) =
      cubicalChainModuleLof _ _ R n (map R (γ.append a) n s) := by
  simp only [pathChainAppend, LinearMap.comp_apply, LinearEquiv.coe_coe,
    cubicalChainModuleEquiv_lof, cubicalChainSumMap_lof, cubicalChainModuleEquiv_symm_lof]

/-- Appending commutes with the loops acting in front. -/
theorem pathChainAppend_smul (γ : MoorePathBetween B b c) (a : B) (x : loopChainAlgebra B a R)
    (σ : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    pathChainAppend R γ a (x • σ) = x • pathChainAppend R γ a σ := by
  induction σ using cubicalChainModule.induction_on with
  | add σ σ' hσ hσ' => rw [smul_add, map_add, hσ, hσ', map_add, smul_add]
  | lof q s =>
    induction x using DirectSum.induction_on with
    | zero => rw [zero_smul, map_zero, zero_smul]
    | add x x' hx hx' => rw [add_smul, map_add, hx, hx', add_smul]
    | of p z =>
      rw [← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof, pathChainAppend_lof,
        pathChainAppend_lof, lof_smul_cubicalChainModuleLof,
        map_leftAct (γ.append a) (fun ω δ ↦ MoorePathBetween.append_smul γ δ ω)]

/-- Appending is a chain map. -/
theorem cubicalChainModuleDifferential_pathChainAppend (γ : MoorePathBetween B b c) (a : B)
    (σ : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    cubicalChainModuleDifferential _ _ R (pathChainAppend R γ a σ) =
      pathChainAppend R γ a (cubicalChainModuleDifferential _ _ R σ) := by
  apply (cubicalChainModuleEquiv _ _ R).injective
  simp only [cubicalChainModuleEquiv_differential, pathChainAppend, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    cubicalChainDifferential_cubicalChainSumMap]

/-! ### Closing up paths into loops -/

variable (R) in
/-- The closing-up map `σ ↦ σ ⋆ γ⁻¹` on chains. -/
def pathChainToLoopChain (γ : MoorePathBetween B b c) :
    cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R →ₗ[R]
      loopChainAlgebra B b R :=
  cubicalChainSumMap R (MoorePathBetween.loopAppendHomotopyEquiv γ).invFun ∘ₗ
    (cubicalChainModuleEquiv _ _ R).toLinearMap

/-- On a homogeneous chain, closing up is the push-forward along concatenation with `γ⁻¹`. -/
@[simp]
theorem pathChainToLoopChain_lof (γ : MoorePathBetween B b c) {n : ℕ}
    (s : NormalizedCubicalChain (MoorePathBetween B b c) R n) :
    pathChainToLoopChain R γ (cubicalChainModuleLof _ _ R n s) =
      cubicalChainLof _ R n (map R (MoorePathBetween.loopAppendHomotopyEquiv γ).invFun n s) := by
  rw [pathChainToLoopChain, LinearMap.comp_apply, LinearEquiv.coe_coe,
    cubicalChainModuleEquiv_lof, cubicalChainSumMap_lof]

/-- Closing up commutes with the loops acting in front. -/
theorem pathChainToLoopChain_smul (γ : MoorePathBetween B b c) (x : loopChainAlgebra B b R)
    (σ : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainToLoopChain R γ (x • σ) = x * pathChainToLoopChain R γ σ := by
  induction σ using cubicalChainModule.induction_on with
  | add σ σ' hσ hσ' => rw [smul_add, map_add, hσ, hσ', map_add, mul_add]
  | lof q s =>
    induction x using DirectSum.induction_on with
    | zero => rw [zero_smul, map_zero, zero_mul]
    | add x x' hx hx' => rw [add_smul, map_add, hx, hx', add_mul]
    | of p z =>
      rw [← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof, pathChainToLoopChain_lof,
        pathChainToLoopChain_lof, cubicalChainLof_mul, map_leftAct
          (MoorePathBetween.loopAppendHomotopyEquiv γ).invFun
          (fun ω δ ↦ MoorePathBetween.loopAppendHomotopyEquiv_symm_smul γ ω δ),
        leftAct_self_eq_mul]

/-- Closing up is a chain map. -/
theorem pathChainToLoopChain_differential (γ : MoorePathBetween B b c)
    (σ : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    cubicalChainDifferential _ R (pathChainToLoopChain R γ σ) =
      pathChainToLoopChain R γ (cubicalChainModuleDifferential _ _ R σ) := by
  rw [pathChainToLoopChain, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    cubicalChainModuleEquiv_differential,
    cubicalChainDifferential_cubicalChainSumMap]

/-- Closing up preserves degrees. -/
theorem pathChainToLoopChain_mem (γ : MoorePathBetween B b c) {i : ℤ}
    {σ : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R}
    (hσ : σ ∈ cubicalChainModuleGrading _ _ R i) :
    pathChainToLoopChain R γ σ ∈ cubicalChainGrading _ R i :=
  cubicalChainSumMap_mem _ (mem_cubicalChainModuleGrading.1 hσ)

/-! ### The loop `γ⁻¹ ⋆ γ` and its retracing chain -/

variable (R) in
/-- The point chain of the Moore loop `γ⁻¹ ⋆ γ` at the end point of `γ`. -/
def loopChainSymmTrans (γ : MoorePathBetween B b c) : loopChainAlgebra B c R :=
  cubicalChainLof _ R 0
    (ofCube _ R (SingularCube.point ((MoorePathBetween.loopHomeomorph c).symm (γ.symm.trans γ))))

/-- The `1`-cube of the retracing loops of `γ⁻¹`, from the unit to `γ⁻¹ ⋆ γ`. -/
private def retraceCube (γ : MoorePathBetween B b c) : SingularCube (MooreLoopSpace B c) 1 :=
  ⟨fun x ↦ γ.symm.retrace (unitInterval.toNNReal (x 0) * γ.toMoorePath.length), by fun_prop⟩

private theorem face_zero_retraceCube (γ : MoorePathBetween B b c) :
    SingularCube.face 0 0 (retraceCube γ) = SingularCube.point 1 := by
  ext x : 1
  simp [retraceCube]

private theorem face_one_retraceCube (γ : MoorePathBetween B b c) :
    SingularCube.face 0 1 (retraceCube γ) =
      SingularCube.point ((MoorePathBetween.loopHomeomorph c).symm (γ.symm.trans γ)) := by
  have hfull : γ.toMoorePath.symm.truncate γ.toMoorePath.length = γ.toMoorePath.symm := by
    simpa only [MoorePath.length_symm] using γ.toMoorePath.symm.truncate_length
  ext x : 1
  apply MooreLoopSpace.ext
  simp [retraceCube, hfull]

variable (R) in
/-- The `1`-chain of the retracing loops of `γ⁻¹`, with the sign that makes its boundary
`[γ⁻¹ ⋆ γ] - 1`. -/
def loopChainRetrace (γ : MoorePathBetween B b c) : loopChainAlgebra B c R :=
  -cubicalChainLof _ R 1 (ofCube _ R (retraceCube γ))

/-- The retracing `1`-chain joins `[γ⁻¹ ⋆ γ]` to the unit. -/
theorem cubicalChainDifferential_loopChainRetrace (γ : MoorePathBetween B b c) :
    cubicalChainDifferential _ R (loopChainRetrace R γ) = loopChainSymmTrans R γ - 1 := by
  rw [loopChainRetrace, map_neg, cubicalChainDifferential_lof_succ, boundary_ofCube,
    Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, face_zero_retraceCube,
    face_one_retraceCube, loopChainSymmTrans, DirectSum.one_def, ← DirectSum.lof_eq_of R,
    NormalizedCubicalChain.gOne_one, one_def, map_sub, neg_sub]

/-- Appending `γ⁻¹` and then `γ` is the right action of the loop `γ⁻¹ ⋆ γ`. -/
theorem pathChainAppend_pathChainAppend_symm (γ : MoorePathBetween B b c) (a : B)
    (σ : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    pathChainAppend R γ a (pathChainAppend R γ.symm a σ) = op (loopChainSymmTrans R γ) • σ := by
  induction σ using cubicalChainModule.induction_on with
  | add σ σ' hσ hσ' => rw [map_add, map_add, hσ, hσ', smul_add]
  | lof q s =>
    rw [pathChainAppend_lof, pathChainAppend_lof, ← LinearMap.comp_apply (map R _ q),
      ← NormalizedCubicalChain.map_comp, loopChainSymmTrans, op_lof_smul_cubicalChainModuleLof,
      act_ofCube_point]
    congr 3
    ext δ : 1
    apply MoorePathBetween.ext
    simp [MoorePath.trans_assoc]

/-- Closing up a chain of paths by `γ⁻¹` and then appending `γ` is the right action of the loop
`γ⁻¹ ⋆ γ`. -/
theorem pathChainToLoopChain_smul_pathChainPoint (γ : MoorePathBetween B b c)
    (σ : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainToLoopChain R γ σ • pathChainPoint R γ = op (loopChainSymmTrans R γ) • σ := by
  induction σ using cubicalChainModule.induction_on with
  | add σ σ' hσ hσ' => rw [map_add, add_smul, hσ, hσ', smul_add]
  | lof q s =>
    rw [pathChainToLoopChain_lof, pathChainPoint, lof_smul_cubicalChainModuleLof,
      leftAct_ofCube_point, ← LinearMap.comp_apply (NormalizedCubicalChain.map R _ q),
      ← NormalizedCubicalChain.map_comp, loopChainSymmTrans, op_lof_smul_cubicalChainModuleLof,
      act_ofCube_point]
    congr 3
    ext δ : 1
    apply MoorePathBetween.ext
    simp [MoorePath.trans_assoc]

/-- Concatenating with the point chain of `γ` is appending `γ`. -/
theorem pathChainConcat_tmul_pathChainPoint (γ : MoorePathBetween B b c)
    (σ : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) σ (pathChainPoint R γ)) =
      pathChainAppend R γ a σ := by
  induction σ using cubicalChainModule.induction_on with
  | add σ σ' hσ hσ' => rw [add_tmul, map_add, hσ, hσ', map_add]
  | lof q s =>
    rw [pathChainConcat_tmul, pathChainPoint, cubicalChainPairing_lof_lof,
      map_crossProduct_ofCube_point, pathChainAppend_lof]
    congr 3
    ext δ : 1
    simp

/-- Acting on a chain of paths from `a` to `b` by the closed-up chain `τ ⋆ γ⁻¹` is concatenating
with `τ` and then appending `γ⁻¹`. -/
theorem op_pathChainToLoopChain_smul (γ : MoorePathBetween B b c)
    (σ : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (τ : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    op (pathChainToLoopChain R γ τ) • σ =
      pathChainAppend R γ.symm a
        (pathChainConcat B a b c R (tmul R (loopChainAlgebra B b R) σ τ)) := by
  induction τ using cubicalChainModule.induction_on with
  | add τ τ' hτ hτ' =>
    rw [map_add, MulOpposite.op_add, add_smul, hτ, hτ', tmul_add, map_add, map_add]
  | lof q t =>
    induction σ using cubicalChainModule.induction_on with
    | add σ σ' hσ hσ' => rw [smul_add, hσ, hσ', add_tmul, map_add, map_add]
    | lof p s =>
      have hcross := NormalizedCubicalChain.map_crossProduct (R := R) (ContinuousMap.id _)
        (MoorePathBetween.loopAppendHomotopyEquiv γ).invFun s t
      rw [NormalizedCubicalChain.map_id, LinearMap.id_apply] at hcross
      rw [pathChainToLoopChain_lof, op_lof_smul_cubicalChainModuleLof, act_def, ← hcross,
        pathChainConcat_tmul, cubicalChainPairing_lof_lof, pathChainAppend_lof,
        ← LinearMap.comp_apply (map R (actMap _ _) (p + q)), ← NormalizedCubicalChain.map_comp,
        ← LinearMap.comp_apply (map R (γ.symm.append a) (p + q)),
        ← NormalizedCubicalChain.map_comp]
      congr 3
      ext δ : 1
      apply MoorePathBetween.ext
      simp [MoorePath.trans_assoc]

end TauCeti
