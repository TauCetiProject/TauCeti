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
it gives two maps, both linear over the chains on the loops acting in front and commuting with
the boundary:

* appending `γ`, `C_*(P_{a→b} B) → C_*(P_{a→c} B)` (`TauCeti.pathChainAppend`);
* closing up a path from `b` to `c` into a loop at `b` by appending the reversal of `γ`,
  `C_*(P_{b→c} B) → C_*(Ω_b B)` (`TauCeti.pathChainToLoopChain`).

Neither appending `γ⁻¹` and then `γ`, nor closing up and then acting on the `0`-chain `[γ]` of `γ`
(`TauCeti.pathChainPoint`), is the identity: both are the push-forward of appending `γ⁻¹` and then
`γ`, which `TauCeti.pathChainAppendHomotopy` joins to the identity. Concatenating with `[γ]` is
appending `γ` (`TauCeti.pathChainConcat_tmul_pathChainPoint`). These are the chain-level inputs
for the change of basepoint of DG local systems.

## Main definitions

* `TauCeti.pathChainPoint R γ`: the `0`-chain of a Moore path.
* `TauCeti.pathChainAppend R γ a`: appending `γ` on chains of paths starting at `a`.
* `TauCeti.pathChainToLoopChain R γ`: closing up chains of paths by `γ⁻¹`.

## Main results

* `TauCeti.pathChainAppend_pathChainAppend_symm`,
  `TauCeti.pathChainToLoopChain_smul_pathChainPoint`: both round trips are the push-forward of
  appending `γ⁻¹` and then `γ`.
* `TauCeti.pathChainConcat_tmul_pathChainPoint`: concatenating with `[γ]` is appending `γ`.
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
/-- The `0`-chain of a path. -/
def pathChainPoint (δ : MoorePathBetween B a b) :
    cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R :=
  cubicalChainModuleLof _ _ R 0 (NormalizedCubicalChain.ofCube _ R (SingularCube.point δ))

/-- The `0`-chain of a path is the class of the constant `0`-cube at the path. -/
theorem pathChainPoint_def (δ : MoorePathBetween B a b) :
    pathChainPoint R δ =
      cubicalChainModuleLof (MoorePathBetween B a b) (MooreLoopSpace B b) R 0
        (NormalizedCubicalChain.ofCube (MoorePathBetween B a b) R (SingularCube.point δ)) :=
  (rfl)

/-- The `0`-chain of a path has degree `0`. -/
theorem pathChainPoint_mem (δ : MoorePathBetween B a b) :
    pathChainPoint R δ ∈
      cubicalChainModuleGrading (MoorePathBetween B a b) (MooreLoopSpace B b) R 0 :=
  mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨0, _, by simp, rfl⟩)

/-- The `0`-chain of a path is a cycle. -/
@[simp]
theorem cubicalChainModuleDifferential_pathChainPoint (δ : MoorePathBetween B a b) :
    cubicalChainModuleDifferential _ _ R (pathChainPoint R δ) = 0 :=
  cubicalChainModuleDifferential_lof_zero _

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

/-- Appending `γ⁻¹` and then `γ` on chains is the push-forward along the composite of the two
appending maps. -/
theorem pathChainAppend_pathChainAppend_symm (γ : MoorePathBetween B b c) (a : B)
    (σ : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    pathChainAppend R γ a (pathChainAppend R γ.symm a σ) =
      cubicalChainModuleLinearMap R ((γ.append a).comp (γ.symm.append a)) σ := by
  induction σ using cubicalChainModule.induction_on with
  | add σ σ' hσ hσ' => rw [map_add, map_add, hσ, hσ', map_add]
  | lof q s =>
    rw [pathChainAppend_lof, pathChainAppend_lof, cubicalChainModuleLinearMap_lof,
      NormalizedCubicalChain.map_comp, LinearMap.comp_apply]

/-! ### Closing up paths into loops -/

variable (R) in
/-- The map `ρ : C_*(P_{a→b} B) → C_*(Ω_a B)` of chains induced by appending the reversal of a
Moore path `δ` from `a` to `b`. -/
def pathChainToLoopChain (δ : MoorePathBetween B a b) :
    cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R →ₗ[R]
      loopChainAlgebra B a R :=
  cubicalChainSumMap R (MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun ∘ₗ
    (cubicalChainModuleEquiv _ _ R).toLinearMap

/-- On a homogeneous chain, `pathChainToLoopChain` is the push-forward of the chain. -/
@[simp]
theorem pathChainToLoopChain_lof (δ : MoorePathBetween B a b) {n : ℕ}
    (c : NormalizedCubicalChain (MoorePathBetween B a b) R n) :
    pathChainToLoopChain R δ (cubicalChainModuleLof _ (MooreLoopSpace B b) R n c) =
      cubicalChainLof (MooreLoopSpace B a) R n
        (NormalizedCubicalChain.map R
          (MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun n c) := by
  simp [pathChainToLoopChain, cubicalChainSumMap_lof]

/-- `pathChainToLoopChain` is linear for the loops at `a` acting in front. -/
theorem pathChainToLoopChain_smul (δ : MoorePathBetween B a b) (α : loopChainAlgebra B a R)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    pathChainToLoopChain R δ (α • x) = α * pathChainToLoopChain R δ x := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, mul_add]
  | lof q c =>
    induction α using DirectSum.induction_on with
    | zero => simp
    | add α α' hα hα' => rw [add_smul, map_add, hα, hα', add_mul]
    | of p y =>
      rw [← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof, pathChainToLoopChain_lof,
        pathChainToLoopChain_lof, cubicalChainLof_mul, NormalizedCubicalChain.map_leftAct _
          (fun ω γ ↦ MoorePathBetween.loopAppendHomotopyEquiv_symm_smul δ ω γ),
        NormalizedCubicalChain.leftAct_eq_mul]

/-- `pathChainToLoopChain` preserves cohomological degree. -/
theorem pathChainToLoopChain_mem (δ : MoorePathBetween B a b) {i : ℤ}
    {x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R}
    (hx : x ∈ cubicalChainModuleGrading (MoorePathBetween B a b) (MooreLoopSpace B b) R i) :
    pathChainToLoopChain R δ x ∈ cubicalChainGrading (MooreLoopSpace B a) R i := by
  rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
  · simp only [map_zero, Submodule.zero_mem]
  · rw [pathChainToLoopChain_lof]
    exact (mem_cubicalChainGrading_iff _ _).2 (Or.inr ⟨n, _, hn, rfl⟩)

/-- `pathChainToLoopChain` commutes with the differentials. -/
theorem pathChainToLoopChain_differential (δ : MoorePathBetween B a b)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    pathChainToLoopChain R δ (cubicalChainModuleDifferential _ _ R x) =
      cubicalChainDifferential (MooreLoopSpace B a) R (pathChainToLoopChain R δ x) := by
  simp only [pathChainToLoopChain, LinearMap.comp_apply, LinearEquiv.coe_coe,
    cubicalChainModuleEquiv_differential, cubicalChainDifferential_cubicalChainSumMap]

/-- Acting on the `0`-chain of `δ` after `pathChainToLoopChain` is the push-forward of appending
`δ⁻¹` and then `δ`. -/
theorem pathChainToLoopChain_smul_pathChainPoint (δ : MoorePathBetween B a b)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    pathChainToLoopChain R δ x • pathChainPoint R δ =
      cubicalChainModuleLinearMap R
        ((MoorePathBetween.append δ a).comp (MoorePathBetween.append δ.symm a)) x := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [map_add, add_smul, hx, hx', map_add]
  | lof q c =>
    have h : ((leftActMap (MooreLoopSpace B a) (MoorePathBetween B a b)).comp
        ((ContinuousMap.id _).prodMk (ContinuousMap.const _ δ))).comp
          (MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun =
        (MoorePathBetween.append δ a).comp (MoorePathBetween.append δ.symm a) :=
      ContinuousMap.ext fun x ↦ MoorePathBetween.ext (by simp [MoorePath.trans_assoc])
    rw [pathChainToLoopChain_lof, pathChainPoint, lof_smul_cubicalChainModuleLof,
      cubicalChainModuleLinearMap_lof, ← cubicalChainModuleLof_cast (Nat.add_zero q),
      NormalizedCubicalChain.leftAct_def, ← NormalizedCubicalChain.map_cast,
      NormalizedCubicalChain.crossProduct_point_right, ← h, NormalizedCubicalChain.map_comp,
      NormalizedCubicalChain.map_comp, LinearMap.comp_apply, LinearMap.comp_apply]

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
        (MoorePathBetween.loopAppendHomotopyEquiv γ).symm.toFun s t
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
