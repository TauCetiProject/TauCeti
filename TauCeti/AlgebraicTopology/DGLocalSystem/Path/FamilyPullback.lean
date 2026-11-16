/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BasepointChange
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Lift

/-!
# Pullback of DG local systems along maps that move the basepoints

A DG local system at a point `a` of a space `B` is a right DG module over `C_*(Ω_a B)`. Tensoring
with the chain bimodule `C_*(P_{a→b} B)` of Moore paths from `a` to `b` moves it to a DG local
system at `b` (`TauCeti.DGLocalSystem.changeBasepoint`), and this ordinary tensor product preserves
quasi-isomorphisms (`TauCeti.DGLocalSystem.isQuasiIso_changeBasepoint_map`).

On a space with a chosen basepoint `b_c` in each path component `c`, a DG local system is a family
of DG local systems at the chosen basepoints (`TauCeti.DGLocalSystemFamily`). A continuous map
`f : B' → B` need not send the chosen basepoints of `B'` to those of `B`. Its pullback
(`TauCeti.DGLocalSystemFamily.pullbackChangeBasepoint`) sends the family `(𝓕_c)` to the family
whose component at `c'` is obtained from `𝓕_{f(c')}` by changing the basepoint from `b_{f(c')}` to
`f(b'_{c'})` and then restricting scalars along
`C_*(Ωf) : C_*(Ω_{b'_{c'}} B') → C_*(Ω_{f(b'_{c'})} B)`. It preserves componentwise
quasi-isomorphisms
(`TauCeti.DGLocalSystemFamily.isQuasiIso_pullbackChangeBasepoint_map`).

Changing the basepoint commutes with pullback, up to a natural quasi-isomorphism. For points
`a, b` of `B'` and a DG local system `M` at `f a`, pushing paths forward along `f` gives the map

`f^*M ⊗ C_*(P_{a→b} B') → f^*(M ⊗ C_*(P_{f a→f b} B))`,  `m ⊗ c ↦ m ⊗ f_* c`

of DG local systems at `b` (`TauCeti.DGLocalSystem.changeBasepointPullbackHom`), natural in `M`
(`TauCeti.DGLocalSystem.changeBasepointPullback`). When `a` and `b` are joined by a Moore path, it
is a quasi-isomorphism (`TauCeti.DGLocalSystem.isQuasiIso_changeBasepointPullbackHom`): for a Moore
path `δ` from `a` to `b`, both sides are homotopy retracts of `M` over the ground ring, through `δ`
and its image `f ∘ δ` (`TauCeti.tensorPathChainAct`), compatibly with the map. Without such a path
the source vanishes while the target need not, since `f a` and `f b` may still be joined in `B`.

The chain-level ingredient is the push-forward of path chains along `f`
(`TauCeti.pathChainMap`), which is semilinear for the loops acting in front and behind, through
`C_*(Ωf)` (`TauCeti.pathChainMap_smul`, `TauCeti.pathChainMap_op_smul`), and commutes with
appending the reversal of a path (`TauCeti.pathChainToLoopChain_pathChainMap`).

## Main definitions

* `TauCeti.pathChainMap R f a b`: the push-forward `C_*(P_{a→b} B') → C_*(P_{f a→f b} B)`.
* `TauCeti.DGLocalSystem.changeBasepoint R a b`: the functor `M ↦ M ⊗ C_*(P_{a→b} B)`.
* `TauCeti.DGLocalSystem.changeBasepointPullback R f a b`: the natural transformation
  `f^*M ⊗ C_*(P_{a→b} B') → f^*(M ⊗ C_*(P_{f a→f b} B))`.
* `TauCeti.DGLocalSystemFamily.pullbackChangeBasepoint R f β'`: the pullback of DG local systems on
  spaces with chosen basepoints along an arbitrary continuous map.

## Main results

* `TauCeti.DGLocalSystem.isQuasiIso_changeBasepoint_map`: changing the basepoint preserves
  quasi-isomorphisms.
* `TauCeti.DGLocalSystem.isQuasiIso_changeBasepointPullbackHom`: changing the basepoint commutes
  with pullback up to quasi-isomorphism.
* `TauCeti.DGLocalSystemFamily.isQuasiIso_pullbackChangeBasepoint_map`: the pullback of families
  preserves componentwise quasi-isomorphisms.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 2 and 7.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe u u' w v

/-! ### Push-forward of path chains -/

section PathChainMap

variable {B : Type u} {B' : Type u'} [TopologicalSpace B] [TopologicalSpace B'] (R : Type w)
  [CommRing R] (f : C(B', B))

/-- The **push-forward of path chains** along `f : B' → B`: the map
`C_*(P_{a→b} B') → C_*(P_{f a→f b} B)` induced by sending a Moore path to its image. -/
def pathChainMap (a b : B') :
    cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R →ₗ[R]
      cubicalChainModule (MoorePathBetween B (f a) (f b)) (MooreLoopSpace B (f b)) R :=
  (cubicalChainModuleEquiv _ _ R).symm.toLinearMap ∘ₗ
    cubicalChainSumMap R (MoorePathBetween.map f) ∘ₗ (cubicalChainModuleEquiv _ _ R).toLinearMap

variable {R f} {a b : B'}

/-- On a homogeneous chain, `pathChainMap` is the push-forward of the chain. -/
@[simp]
theorem pathChainMap_lof {n : ℕ} (c : NormalizedCubicalChain (MoorePathBetween B' a b) R n) :
    pathChainMap R f a b (cubicalChainModuleLof _ (MooreLoopSpace B' b) R n c) =
      cubicalChainModuleLof _ (MooreLoopSpace B (f b)) R n
        (NormalizedCubicalChain.map R (MoorePathBetween.map f) n c) := by
  simp [pathChainMap, cubicalChainSumMap_lof]

/-- `pathChainMap` commutes with the differentials. -/
theorem pathChainMap_differential
    (x : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    pathChainMap R f a b (cubicalChainModuleDifferential _ _ R x) =
      cubicalChainModuleDifferential _ _ R (pathChainMap R f a b x) := by
  simp only [pathChainMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    cubicalChainModuleEquiv_differential, ← cubicalChainDifferential_cubicalChainSumMap,
    cubicalChainModuleEquiv_symm_differential]

/-- `pathChainMap` preserves the cohomological degree. -/
theorem pathChainMap_mem {i : ℤ}
    {x : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R}
    (hx : x ∈ cubicalChainModuleGrading (MoorePathBetween B' a b) (MooreLoopSpace B' b) R i) :
    pathChainMap R f a b x ∈
      cubicalChainModuleGrading (MoorePathBetween B (f a) (f b)) (MooreLoopSpace B (f b)) R i := by
  rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
  · simp only [map_zero, Submodule.zero_mem]
  · rw [pathChainMap_lof]
    exact mem_cubicalChainModuleGrading_iff.2 (Or.inr ⟨n, _, hn, rfl⟩)

/-- `pathChainMap` is semilinear for the loops acting in front, through `C_*(Ωf)`. -/
theorem pathChainMap_smul (α : loopChainAlgebra B' a R)
    (x : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    pathChainMap R f a b (α • x) = loopChainMap R f rfl α • pathChainMap R f a b x := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
  | lof q c =>
    induction α using DirectSum.induction_on with
    | zero => simp
    | add α α' hα hα' => rw [add_smul, map_add, hα, hα', map_add, add_smul]
    | of p y =>
      rw [← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof, pathChainMap_lof,
        pathChainMap_lof, loopChainMap_lof, lof_smul_cubicalChainModuleLof,
        NormalizedCubicalChain.map_leftAct_map _ (MooreLoopSpace.map f rfl).toContinuousMap
          (MoorePathBetween.map_smul f)]

/-- `pathChainMap` is semilinear for the loops acting behind, through `C_*(Ωf)`. -/
theorem pathChainMap_op_smul (α : loopChainAlgebra B' b R)
    (x : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    pathChainMap R f a b (op α • x) = op (loopChainMap R f rfl α) • pathChainMap R f a b x := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
  | lof q c =>
    induction α using DirectSum.induction_on with
    | zero => simp
    | add α α' hα hα' =>
      rw [MulOpposite.op_add, add_smul, map_add, hα, hα', map_add, MulOpposite.op_add, add_smul]
    | of p y =>
      rw [← DirectSum.lof_eq_of R, op_lof_smul_cubicalChainModuleLof, pathChainMap_lof,
        pathChainMap_lof, loopChainMap_lof, op_lof_smul_cubicalChainModuleLof,
        NormalizedCubicalChain.map_act_map _ (MooreLoopSpace.map f rfl).toContinuousMap
          (fun ω γ ↦ MoorePathBetween.map_op_smul f ω γ)]

/-- `pathChainMap` sends the `0`-chain of a path to the `0`-chain of its image. -/
@[simp]
theorem pathChainMap_pathChainPoint (δ : MoorePathBetween B' a b) :
    pathChainMap R f a b (pathChainPoint R δ) = pathChainPoint R (MoorePathBetween.map f δ) := by
  rw [pathChainPoint_def, pathChainPoint_def, pathChainMap_lof, NormalizedCubicalChain.map_ofCube]
  congr 2
  exact ContinuousMap.ext fun t ↦ by simp only [ContinuousMap.comp_apply, SingularCube.point_apply]

/-- Appending the reversal of the image of `δ` after pushing forward is pushing forward after
appending the reversal of `δ`. -/
theorem pathChainToLoopChain_pathChainMap (δ : MoorePathBetween B' a b)
    (x : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    pathChainToLoopChain R (MoorePathBetween.map f δ) (pathChainMap R f a b x) =
      loopChainMap R f rfl (pathChainToLoopChain R δ x) := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | lof q c =>
    have h : (MoorePathBetween.loopAppendHomotopyEquiv (MoorePathBetween.map f δ)).symm.toFun.comp
        (MoorePathBetween.map f) =
          (MooreLoopSpace.map f rfl).toContinuousMap.comp
            (MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun :=
      ContinuousMap.ext fun γ ↦ MooreLoopSpace.ext (by simp)
    rw [pathChainMap_lof, pathChainToLoopChain_lof, pathChainToLoopChain_lof, loopChainMap_lof,
      ← LinearMap.comp_apply (NormalizedCubicalChain.map R _ q), ← NormalizedCubicalChain.map_comp,
      h, NormalizedCubicalChain.map_comp, LinearMap.comp_apply]

end PathChainMap

/-! ### Changing the basepoint -/

namespace DGLocalSystem

variable {B : Type u} [TopologicalSpace B] (R : Type w) [CommRing R]

/-- **Changing the basepoint** of DG local systems from `a` to `b`: tensoring with the chain
bimodule `C_*(P_{a→b} B)` of Moore paths from `a` to `b`. -/
abbrev changeBasepoint (a b : B) : DGLocalSystem.{v} B a R ⥤ DGLocalSystem.{max v u w} B b R where
  obj M := DGRightModuleCat.tensorBimoduleObj M (pathChainBimodule B a b R)
  map g := DGRightModuleCat.tensorBimoduleMap g (𝟙 (pathChainBimodule B a b R))
  map_id M := DGRightModuleCat.tensorBimoduleMap_id M _
  map_comp g g' := by
    rw [← DGRightModuleCat.tensorBimoduleMap_comp, Category.comp_id]

variable {R} {a b : B}

/-- **Changing the basepoint preserves quasi-isomorphisms.** -/
theorem isQuasiIso_changeBasepoint_map {M N : DGLocalSystem.{v} B a R} {g : M ⟶ N}
    (hg : DGRightModuleCat.IsQuasiIso g) :
    DGRightModuleCat.IsQuasiIso ((changeBasepoint R a b).map g) :=
  isQuasiIso_tensorBimoduleMap_pathChainBimodule hg

end DGLocalSystem

/-! ### Changing the basepoint commutes with pullback -/

namespace DGLocalSystem

open BalancedTensorProduct DGRightModuleCat

variable {B B' : Type u} [TopologicalSpace B] [TopologicalSpace B'] {R : Type w} [CommRing R]
  (f : C(B', B)) {a b : B'} (M : DGLocalSystem.{v} B (f a) R)

omit [TopologicalSpace B'] in
/-- The loops at `b` act on `M ⊗ C_*(P_{a→b} B)` through the path factor. -/
private theorem op_smul_tmul_changeBasepoint {a b : B} (N : DGLocalSystem.{v} B a R)
    (x : loopChainAlgebra B b R) (n : N)
    (c : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    letI := (tensorBimoduleObj N (pathChainBimodule B a b R)).moduleOp
    (op x • (tmul R (loopChainAlgebra B a R) n c :
      tensorBimoduleObj N (pathChainBimodule B a b R))) =
      tmul R (loopChainAlgebra B a R) n (op x • c) :=
  smul_tmul_right _ _ _ _

/-- Pushing paths forward along `f` is balanced over the loops at `a`, acting on `f^*M` through
`C_*(Ωf)`. -/
private theorem tmul_restrictScalarsEquiv_smul (α : loopChainAlgebra B' a R)
    (m : (pullback R f rfl).obj M)
    (c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    tmul R (loopChainAlgebra B (f a) R) (restrictScalarsEquiv (loopChainMap R f rfl) M (op α • m))
        (pathChainMap R f a b c) =
      tmul R (loopChainAlgebra B (f a) R) (restrictScalarsEquiv (loopChainMap R f rfl) M m)
        (pathChainMap R f a b (α • c)) := by
  rw [restrictScalarsEquiv_smul, unop_op, pathChainMap_smul]
  exact balance R (loopChainAlgebra B (f a) R) _ _ _

/-- The bilinear map `(m, c) ↦ m ⊗ f_* c` underlying `changeBasepointPullbackHom`, before
restriction. -/
private def changeBasepointPullbackBilin₀ :
    (pullback R f rfl).obj M →ₗ[R]
      cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R →ₗ[R]
        tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R) :=
  LinearMap.mk₂ R (fun m c ↦ tmul R (loopChainAlgebra B (f a) R)
      (restrictScalarsEquiv (loopChainMap R f rfl) M m) (pathChainMap R f a b c))
    (fun m m' c ↦ by rw [map_add, add_tmul]) (fun r m c ↦ by rw [map_smul, smul_tmul])
    (fun m c c' ↦ by rw [map_add, tmul_add]) (fun r m c ↦ by rw [map_smul, tmul_smul])

/-- The bilinear map `(m, c) ↦ m ⊗ f_* c` underlying `changeBasepointPullbackHom`. -/
private def changeBasepointPullbackBilin :
    (pullback R f rfl).obj M →ₗ[R]
      cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R →ₗ[R]
        (pullback R f (rfl : f b = f b)).obj
          (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R)) :=
  (changeBasepointPullbackBilin₀ f M).compr₂
    (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
      (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).symm.toLinearMap

private theorem restrictScalarsEquiv_changeBasepointPullbackBilin (m : (pullback R f rfl).obj M)
    (c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
        (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))
        (changeBasepointPullbackBilin f M m c) =
      tmul R (loopChainAlgebra B (f a) R) (restrictScalarsEquiv (loopChainMap R f rfl) M m)
        (pathChainMap R f a b c) :=
  LinearEquiv.apply_symm_apply _ _

private theorem changeBasepointPullbackBilin_op_smul (α : loopChainAlgebra B' b R)
    (m : (pullback R f rfl).obj M)
    (c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    changeBasepointPullbackBilin f M m (op α • c) =
      op α • changeBasepointPullbackBilin f M m c := by
  apply (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
    (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).injective
  rw [restrictScalarsEquiv_changeBasepointPullbackBilin, restrictScalarsEquiv_smul, unop_op,
    restrictScalarsEquiv_changeBasepointPullbackBilin, pathChainMap_op_smul,
    op_smul_tmul_changeBasepoint]

private theorem changeBasepointPullbackBilin_mem {p q : ℤ} {m : (pullback R f rfl).obj M}
    {c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R}
    (hm : m ∈ ((pullback R f rfl).obj M).grading p)
    (hc : c ∈ cubicalChainModuleGrading (MoorePathBetween B' a b) (MooreLoopSpace B' b) R q) :
    changeBasepointPullbackBilin f M m c ∈
      ((pullback R f (rfl : f b = f b)).obj
        (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).grading (p + q) := by
  rw [mem_restrictScalars_obj_grading, restrictScalarsEquiv_changeBasepointPullbackBilin]
  exact tmul_mem_tensorBimoduleObj_grading
    ((mem_restrictScalars_obj_grading (loopChainMap R f rfl) M p m).1 hm) (pathChainMap_mem hc)

private theorem differential_changeBasepointPullbackBilin {p : ℤ} {m : (pullback R f rfl).obj M}
    (hm : m ∈ ((pullback R f rfl).obj M).grading p)
    (c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    ((pullback R f (rfl : f b = f b)).obj
        (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).differential
        (changeBasepointPullbackBilin f M m c) =
      changeBasepointPullbackBilin f M (((pullback R f rfl).obj M).differential m) c +
        p.negOnePow • changeBasepointPullbackBilin f M m
          (cubicalChainModuleDifferential _ _ R c) := by
  apply (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
    (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).injective
  -- Rewriting is avoided: matching the pattern `e (φ m c)` against the other values of `e` would
  -- unfold the bilinear map. The three values are computed separately and assembled instead.
  have e1 := restrictScalarsEquiv_changeBasepointPullbackBilin f M m c
  have e2 := (restrictScalarsEquiv_changeBasepointPullbackBilin f M
    (((pullback R f rfl).obj M).differential m) c).trans
      (congrArg (fun x ↦ tmul R (loopChainAlgebra B (f a) R) x (pathChainMap R f a b c))
        (restrictScalarsEquiv_differential _ _ m))
  have e3 := (restrictScalarsEquiv_changeBasepointPullbackBilin f M m
    (cubicalChainModuleDifferential _ _ R c)).trans
      (congrArg (tmul R (loopChainAlgebra B (f a) R)
        (restrictScalarsEquiv (loopChainMap R f rfl) M m)) (pathChainMap_differential c))
  refine (restrictScalarsEquiv_differential _ _ _).trans <| (congrArg _ e1).trans <|
    (tensorBimoduleObj_differential_tmul
      ((mem_restrictScalars_obj_grading (loopChainMap R f rfl) M p m).1 hm) _).trans ?_
  refine (congrArg₂ (· + ·) e2.symm (congrArg (p.negOnePow • ·) e3.symm)).trans ?_
  refine Eq.trans ?_ (map_add _ _ _).symm
  refine congrArg _ ?_
  rw [Units.smul_def, Units.smul_def]
  exact (map_zsmul _ _ _).symm

/-- **Changing the basepoint commutes with pullback**: for a map `f : B' → B`, points `a, b` of
`B'` and a DG local system `M` at `f a`, the morphism of DG local systems at `b`

`f^*M ⊗ C_*(P_{a→b} B') → f^*(M ⊗ C_*(P_{f a→f b} B))`,  `m ⊗ c ↦ m ⊗ f_* c`,

pushing paths forward along `f`. -/
def changeBasepointPullbackHom :
    (changeBasepoint R a b).obj ((pullback R f rfl).obj M) ⟶
      (pullback R f (rfl : f b = f b)).obj ((changeBasepoint R (f a) (f b)).obj M) :=
  (DGBimoduleCat.tensorLift
    (P := ((pullback R f (rfl : f b = f b)).obj
      (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).toScalarBimodule)
    (changeBasepointPullbackBilin f M)
    (fun α m c ↦ (restrictScalarsEquiv _ _).injective <| by
      rw [restrictScalarsEquiv_changeBasepointPullbackBilin,
        restrictScalarsEquiv_changeBasepointPullbackBilin]
      exact tmul_restrictScalarsEquiv_smul f M α m c)
    (fun r m c ↦ LinearMap.map_smul₂ _ r m c)
    (fun α m c ↦ changeBasepointPullbackBilin_op_smul f M α m c)
    (fun hm hc ↦ changeBasepointPullbackBilin_mem f M hm hc)
    (fun hm c ↦ differential_changeBasepointPullbackBilin f M hm c)).1

variable {f M}

private theorem changeBasepointPullbackHom_tmul (m : (pullback R f rfl).obj M)
    (c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    changeBasepointPullbackHom f M (tmul R (loopChainAlgebra B' a R) m c) =
      changeBasepointPullbackBilin f M m c := by
  rw [changeBasepointPullbackHom]
  exact DGBimoduleCat.tensorLift_tmul (M := ((pullback R f rfl).obj M).toScalarBimodule)
    (N := pathChainBimodule B' a b R) _ _ _ _ _ _ m c

/-- On a pure tensor, `changeBasepointPullbackHom` pushes the path factor forward along `f`:
`m ⊗ c ↦ m ⊗ f_* c`. -/
theorem restrictScalarsEquiv_changeBasepointPullbackHom_tmul (m : (pullback R f rfl).obj M)
    (c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
        (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))
        (changeBasepointPullbackHom f M (tmul R (loopChainAlgebra B' a R) m c)) =
      tmul R (loopChainAlgebra B (f a) R) (restrictScalarsEquiv (loopChainMap R f rfl) M m)
        (pathChainMap R f a b c) :=
  (congrArg _ (changeBasepointPullbackHom_tmul m c)).trans
    (restrictScalarsEquiv_changeBasepointPullbackBilin f M m c)

variable (f M) in
/-- `changeBasepointPullbackHom` is natural in the DG local system. -/
theorem changeBasepointPullbackHom_naturality {N : DGLocalSystem.{v} B (f a) R} (g : M ⟶ N) :
    (changeBasepoint R a b).map ((pullback R f rfl).map g) ≫ changeBasepointPullbackHom f N =
      changeBasepointPullbackHom f M ≫
        (pullback R f (rfl : f b = f b)).map ((changeBasepoint R (f a) (f b)).map g) := by
  refine hom_ext fun z ↦ ?_
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => rw [map_add, map_add, hz, hz']
  | ht m c =>
    apply (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
      (tensorBimoduleObj N (pathChainBimodule B (f a) (f b) R))).injective
    rw [DGRightModuleCat.comp_apply, DGRightModuleCat.comp_apply]
    refine (congrArg (fun z ↦ restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
      (tensorBimoduleObj N (pathChainBimodule B (f a) (f b) R)) (changeBasepointPullbackHom f N z))
        (tensorBimoduleMap_tmul _ _ m c)).trans ?_
    refine (restrictScalarsEquiv_changeBasepointPullbackHom_tmul (f := f) (M := N) _ _).trans ?_
    refine Eq.trans ?_ (restrictScalars_map_apply (loopChainMap R f (rfl : f b = f b))
      ((changeBasepoint R (f a) (f b)).map g) _).symm
    refine Eq.trans ?_ (congrArg ((changeBasepoint R (f a) (f b)).map g)
      (restrictScalarsEquiv_changeBasepointPullbackHom_tmul (f := f) (M := M) m c)).symm
    refine Eq.trans ?_ (tensorBimoduleMap_tmul _ _ _ _).symm
    exact congrArg₂ (tmul R (loopChainAlgebra B (f a) R)) (restrictScalars_map_apply _ g m)
      (by rw [DGBimoduleCat.id_apply, DGBimoduleCat.id_apply])

variable (R f a b) in
/-- **Changing the basepoint commutes with pullback**, as a natural transformation
`f^*(-) ⊗ C_*(P_{a→b} B') ⟶ f^*((-) ⊗ C_*(P_{f a→f b} B))` with components
`TauCeti.DGLocalSystem.changeBasepointPullbackHom`. -/
def changeBasepointPullback :
    pullback.{v} R f (rfl : f a = f a) ⋙ changeBasepoint R a b ⟶
      changeBasepoint R (f a) (f b) ⋙ pullback R f (rfl : f b = f b) where
  app M := changeBasepointPullbackHom f M
  naturality _ _ g := changeBasepointPullbackHom_naturality f _ g

@[simp]
theorem changeBasepointPullback_app :
    (changeBasepointPullback R f a b).app M = changeBasepointPullbackHom f M :=
  (rfl)

/-- `changeBasepointPullbackHom` is compatible with the retractions `m ⊗ c ↦ m · ρ(c)` of both
sides onto `M`, through a path `δ` and its image. -/
private theorem tensorPathChainAct_changeBasepointPullbackHom (δ : MoorePathBetween B' a b)
    (x : (changeBasepoint R a b).obj ((pullback R f rfl).obj M)) :
    tensorPathChainAct M (MoorePathBetween.map f δ)
        (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
          (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))
          (changeBasepointPullbackHom f M x)) =
      restrictScalarsEquiv (loopChainMap R f rfl) M
        (tensorPathChainAct ((pullback R f rfl).obj M) δ x) := by
  induction x using BalancedTensorProduct.induction_on with
  | ha x x' hx hx' => simp only [map_add, hx, hx']
  | ht m c =>
    exact ((congrArg (tensorPathChainAct M (MoorePathBetween.map f δ))
      (restrictScalarsEquiv_changeBasepointPullbackHom_tmul m c)).trans <|
        (tensorPathChainAct_tmul M _ _ _).trans <|
          congrArg (fun α ↦ op α • restrictScalarsEquiv (loopChainMap R f rfl) M m)
            (pathChainToLoopChain_pathChainMap δ c)).trans
      ((congrArg (restrictScalarsEquiv (loopChainMap R f rfl) M)
        (tensorPathChainAct_tmul _ δ m c)).trans (restrictScalarsEquiv_smul _ _ _ _)).symm

/-- `changeBasepointPullbackHom` is compatible with the sections `m ↦ m ⊗ [δ]` of both sides,
through a path `δ` and its image. -/
private theorem changeBasepointPullbackHom_tensorPathChainPoint (δ : MoorePathBetween B' a b)
    (m : M) :
    changeBasepointPullbackHom f M (tensorPathChainPoint ((pullback R f rfl).obj M) δ
        ((restrictScalarsEquiv (loopChainMap R f rfl) M).symm m)) =
      (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
          (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).symm
        (tensorPathChainPoint M (MoorePathBetween.map f δ) m) := by
  apply (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
    (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).injective
  exact ((congrArg (fun z ↦ restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
      (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R)) (changeBasepointPullbackHom f M z))
    (tensorPathChainPoint_apply _ δ _)).trans <|
      (restrictScalarsEquiv_changeBasepointPullbackHom_tmul _ _).trans <|
        congrArg₂ (tmul R (loopChainAlgebra B (f a) R)) (LinearEquiv.apply_symm_apply _ m)
          (pathChainMap_pathChainPoint δ)).trans
    ((LinearEquiv.apply_symm_apply _ _).trans (tensorPathChainPoint_apply M _ m)).symm

variable (f M) in
/-- **Changing the basepoint commutes with pullback up to quasi-isomorphism**: if `a` and `b` are
joined by a Moore path, the morphism `f^*M ⊗ C_*(P_{a→b} B') → f^*(M ⊗ C_*(P_{f a→f b} B))` is a
quasi-isomorphism. Both sides are homotopy retracts of `M` over the ground ring, through a Moore
path `δ` from `a` to `b` and its image `f ∘ δ`, compatibly with the morphism. The hypothesis
cannot be dropped: without a path from `a` to `b` the source vanishes, while the target need
not. -/
theorem isQuasiIso_changeBasepointPullbackHom (h : Nonempty (MoorePathBetween B' a b)) :
    IsQuasiIso (changeBasepointPullbackHom (b := b) f M) := by
  obtain ⟨δ⟩ := h
  let e := restrictScalarsEquiv (loopChainMap R f (rfl : f a = f a)) M
  let e' := restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
    (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))
  let N := (pullback R f (rfl : f a = f a)).obj M
  let δ' := MoorePathBetween.map f δ
  -- Instance search does not see the structures of a tensor product through its carrier.
  let := ((changeBasepoint R a b).obj N).moduleOp
  let := ((changeBasepoint R a b).obj N).scalarTower
  let := ((changeBasepoint R a b).obj N).gradedSMul
  let := ((pullback R f (rfl : f b = f b)).obj ((changeBasepoint R (f a) (f b)).obj M)).gradedSMul
  refine DGRightModuleHom.isQuasiIso_of_homotopyRetract (changeBasepointPullbackHom f M)
    (dM₀ := M.differential) (dN₀ := M.differential) LinearMap.id
    (fun x y _ hxy ↦ ⟨y, 0, hxy.symm, by rw [map_zero, add_zero, LinearMap.id_apply]⟩)
    (e.toLinearMap ∘ₗ tensorPathChainAct N δ) (tensorPathChainPoint N δ ∘ₗ e.symm.toLinearMap)
    (tensorPathChainHomotopy N δ)
    (tensorPathChainAct M δ' ∘ₗ e'.toLinearMap) (e'.symm.toLinearMap ∘ₗ tensorPathChainPoint M δ')
    (e'.symm.toLinearMap ∘ₗ tensorPathChainHomotopy M δ' ∘ₗ e'.toLinearMap)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  -- The goals are closed by explicit terms: rewriting would match the pattern against the other
  -- values of the same equivalences and unfold the tensor products.
  · exact fun x ↦ (restrictScalarsEquiv_differential _ _ _).symm.trans
      (congrArg e (differential_tensorPathChainAct δ x))
  · exact fun x ↦ (differential_tensorPathChainPoint δ _).trans
      (congrArg _ (restrictScalarsEquiv_symm_differential _ _ _))
  · exact fun y ↦ (differential_tensorPathChainAct δ' _).trans
      (congrArg _ (restrictScalarsEquiv_differential _ _ _).symm)
  · exact fun y ↦ (restrictScalarsEquiv_symm_differential _ _ _).trans
      (congrArg e'.symm (differential_tensorPathChainPoint δ' y))
  · exact fun x ↦ (congrArg _ (e.symm_apply_apply _)).trans
      (tensorPathChainPoint_tensorPathChainAct δ x)
  · exact fun y ↦ (congrArg e'.symm (tensorPathChainPoint_tensorPathChainAct δ' (e' y))).trans
      ((map_add _ _ _).trans (congrArg₂ (· + ·) ((map_add _ _ _).trans
        (congrArg₂ (· + ·) (e'.symm_apply_apply y)
          (restrictScalarsEquiv_symm_differential _ _ _).symm))
        (congrArg (fun z ↦ e'.symm (tensorPathChainHomotopy M δ' z))
          (restrictScalarsEquiv_differential _ _ _).symm)))
  · exact tensorPathChainAct_changeBasepointPullbackHom δ
  · exact changeBasepointPullbackHom_tensorPathChainPoint δ

end DGLocalSystem

/-! ### Pullback of families along an arbitrary map -/

section Family

variable {B : Type u} {B' : Type u'} [TopologicalSpace B] [TopologicalSpace B'] (R : Type w)
  [CommRing R] {β : PathComponentBasepoints B}

namespace DGLocalSystemFamily

/-- The **pullback of DG local systems along an arbitrary map** `f : B' → B` of spaces with
chosen basepoints. The component at a path component `c'` of `B'` is obtained from the component
`𝓕_{f(c')}` by changing the basepoint from the chosen basepoint `b_{f(c')}` to `f(b'_{c'})` and
restricting scalars along `C_*(Ωf)` at `b'_{c'}`. -/
def pullbackChangeBasepoint (f : C(B', B)) (β' : PathComponentBasepoints B') :
    DGLocalSystemFamily.{v} β R ⥤ DGLocalSystemFamily.{max v u w} β' R :=
  @Functor.pi' _ (fun c' ↦ DGLocalSystem.{max v u w} B' (β'.point c') R) (fun _ ↦ inferInstance) _
    _ fun c' ↦
      @Pi.eval _ (fun c ↦ DGLocalSystem.{v} B (β.point c) R) (fun _ ↦ inferInstance)
          (ZerothHomotopy.mk (f (β'.point c'))) ⋙
        DGLocalSystem.changeBasepoint R (β.point (ZerothHomotopy.mk (f (β'.point c'))))
          (f (β'.point c')) ⋙
        DGLocalSystem.pullback R f rfl

variable {R}

/-- The component of the pullback of a family at `c'`. -/
@[simp]
theorem pullbackChangeBasepoint_obj (f : C(B', B)) (β' : PathComponentBasepoints B')
    (𝓕 : DGLocalSystemFamily.{v} β R)
    (c' : ZerothHomotopy B') :
    (pullbackChangeBasepoint R f β').obj 𝓕 c' =
      (DGLocalSystem.pullback R f rfl).obj
        ((DGLocalSystem.changeBasepoint R (β.point (ZerothHomotopy.mk (f (β'.point c'))))
          (f (β'.point c'))).obj (𝓕 (ZerothHomotopy.mk (f (β'.point c'))))) :=
  (rfl)

/-- The component of the pullback of a morphism of families at `c'`. -/
@[simp]
theorem pullbackChangeBasepoint_map (f : C(B', B)) (β' : PathComponentBasepoints B')
    {𝓕 𝓖 : DGLocalSystemFamily.{v} β R}
    (φ : 𝓕 ⟶ 𝓖) (c' : ZerothHomotopy B') :
    (pullbackChangeBasepoint R f β').map φ c' =
      eqToHom (pullbackChangeBasepoint_obj f β' 𝓕 c') ≫
        (DGLocalSystem.pullback R f rfl).map
          ((DGLocalSystem.changeBasepoint R (β.point (ZerothHomotopy.mk (f (β'.point c'))))
            (f (β'.point c'))).map (φ (ZerothHomotopy.mk (f (β'.point c'))))) ≫
          eqToHom (pullbackChangeBasepoint_obj f β' 𝓖 c').symm :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- **The pullback of families preserves quasi-isomorphisms**: if every component of a morphism of
families is a quasi-isomorphism, so is every component of its pullback. -/
theorem isQuasiIso_pullbackChangeBasepoint_map (f : C(B', B)) (β' : PathComponentBasepoints B')
    {𝓕 𝓖 : DGLocalSystemFamily.{v} β R} {φ : 𝓕 ⟶ 𝓖}
    (hφ : ∀ c, DGRightModuleCat.IsQuasiIso (φ c)) (c' : ZerothHomotopy B') :
    DGRightModuleCat.IsQuasiIso ((pullbackChangeBasepoint R f β').map φ c') :=
  DGRightModuleCat.isQuasiIso_restrictScalars_map _
    (DGLocalSystem.isQuasiIso_changeBasepoint_map (hφ _))

end DGLocalSystemFamily

end Family

end TauCeti

end
