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
system at `b` (`TauCeti.DGLocalSystem.basepointChange`). Together with restriction of scalars
along `C_*(Ωf)`, this gives the pullback of families of DG local systems along maps that do not
preserve the chosen basepoints (`TauCeti.DGLocalSystemFamily.pullbackBasepointChange`).

Changing the basepoint commutes with pullback, up to a natural quasi-isomorphism. For points
`a, b` of `B'` and a DG local system `M` at `f a`, pushing paths forward along `f` gives the map

`f^*M ⊗ C_*(P_{a→b} B') → f^*(M ⊗ C_*(P_{f a→f b} B))`,  `m ⊗ c ↦ m ⊗ f_* c`

of DG local systems at `b` (`TauCeti.DGLocalSystem.changeBasepointPullbackHom`), natural in `M`
(`TauCeti.DGLocalSystem.changeBasepointPullback`). When `a` and `b` are joined by a Moore path, it
is a quasi-isomorphism (`TauCeti.DGLocalSystem.isQuasiIso_changeBasepointPullbackHom`): for a Moore
path `δ` from `a` to `b`, both sides are homotopy retracts of `M` over the ground ring, through `δ`
and its image `f ∘ δ` (`TauCeti.tensorPathChainAct`), compatibly with the map. Without such a path
the source vanishes while the target need not, since `f a` and `f b` may still be joined in `B`.

The chain-level ingredient is the push-forward of path chains along `f`, the map
`TauCeti.cubicalChainModuleLinearMap` induced by `TauCeti.MoorePathBetween.map f`. It is
semilinear for the loops acting in front and behind, through `C_*(Ωf)`
(`TauCeti.cubicalChainModuleLinearMap_moorePathBetweenMap_smul`,
`TauCeti.cubicalChainModuleLinearMap_moorePathBetweenMap_op_smul`), and commutes with appending
the reversal of a path (`TauCeti.pathChainToLoopChain_cubicalChainModuleLinearMap`).

## Main definitions

* `TauCeti.DGLocalSystem.changeBasepointPullback R f a b`: the natural transformation
  `f^*M ⊗ C_*(P_{a→b} B') → f^*(M ⊗ C_*(P_{f a→f b} B))`.

## Main results

* `TauCeti.DGLocalSystem.isQuasiIso_changeBasepointPullbackHom`: changing the basepoint commutes
  with pullback up to quasi-isomorphism.

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
        (cubicalChainModuleLinearMap (G' := MooreLoopSpace B (f b)) R
          (MoorePathBetween.map f) c) =
      tmul R (loopChainAlgebra B (f a) R) (restrictScalarsEquiv (loopChainMap R f rfl) M m)
        (cubicalChainModuleLinearMap (G' := MooreLoopSpace B (f b)) R
          (MoorePathBetween.map f) (α • c)) := by
  rw [restrictScalarsEquiv_smul, unop_op, cubicalChainModuleLinearMap_moorePathBetweenMap_smul f]
  exact balance R (loopChainAlgebra B (f a) R) _ _ _

/-- The bilinear map `(m, c) ↦ m ⊗ f_* c` underlying `changeBasepointPullbackHom`, before
restriction. -/
private def changeBasepointPullbackBilin₀ :
    (pullback R f rfl).obj M →ₗ[R]
      cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R →ₗ[R]
        tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R) :=
  LinearMap.mk₂ R (fun m c ↦ tmul R (loopChainAlgebra B (f a) R)
      (restrictScalarsEquiv (loopChainMap R f rfl) M m)
      (cubicalChainModuleLinearMap (G' := MooreLoopSpace B (f b)) R (MoorePathBetween.map f) c))
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
        (cubicalChainModuleLinearMap (G' := MooreLoopSpace B (f b)) R
          (MoorePathBetween.map f) c) :=
  LinearEquiv.apply_symm_apply _ _

private theorem changeBasepointPullbackBilin_op_smul (α : loopChainAlgebra B' b R)
    (m : (pullback R f rfl).obj M)
    (c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    changeBasepointPullbackBilin f M m (op α • c) =
      op α • changeBasepointPullbackBilin f M m c := by
  apply (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
    (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).injective
  rw [restrictScalarsEquiv_changeBasepointPullbackBilin, restrictScalarsEquiv_smul, unop_op,
    restrictScalarsEquiv_changeBasepointPullbackBilin,
    cubicalChainModuleLinearMap_moorePathBetweenMap_op_smul f, op_smul_tmul_changeBasepoint]

private theorem changeBasepointPullbackBilin_mem {p q : ℤ} {m : (pullback R f rfl).obj M}
    {c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R}
    (hm : m ∈ ((pullback R f rfl).obj M).grading p)
    (hc : c ∈ cubicalChainModuleGrading (MoorePathBetween B' a b) (MooreLoopSpace B' b) R q) :
    changeBasepointPullbackBilin f M m c ∈
      ((pullback R f (rfl : f b = f b)).obj
        (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).grading (p + q) := by
  rw [mem_restrictScalars_obj_grading, restrictScalarsEquiv_changeBasepointPullbackBilin]
  exact tmul_mem_tensorBimoduleObj_grading
    ((mem_restrictScalars_obj_grading (loopChainMap R f rfl) M p m).1 hm)
    (cubicalChainModuleLinearMap_mem _ hc)

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
  -- Writing `e` for the restriction equivalences, both sides are
  -- `d (e m) ⊗ f_* c + (-1)^p e m ⊗ f_* (d c)`: by the Leibniz rule in the tensor product on the
  -- left, and `e ∘ d = d ∘ e` and `d ∘ f_* = f_* ∘ d` on the right. The three values of `e ∘ φ`
  -- are computed separately and assembled as terms: rewriting with the Leibniz rule or with
  -- `map_add` here times out unifying the carriers of the tensor product and its restriction.
  have e1 := restrictScalarsEquiv_changeBasepointPullbackBilin f M m c
  have e2 := (restrictScalarsEquiv_changeBasepointPullbackBilin f M
    (((pullback R f rfl).obj M).differential m) c).trans
      (congrArg (fun x ↦ tmul R (loopChainAlgebra B (f a) R) x
        (cubicalChainModuleLinearMap (G' := MooreLoopSpace B (f b)) R (MoorePathBetween.map f) c))
        (restrictScalarsEquiv_differential _ _ m))
  have e3 := (restrictScalarsEquiv_changeBasepointPullbackBilin f M m
    (cubicalChainModuleDifferential _ _ R c)).trans
      (congrArg (tmul R (loopChainAlgebra B (f a) R)
        (restrictScalarsEquiv (loopChainMap R f rfl) M m))
        (cubicalChainModuleDifferential_linearMap _ c).symm)
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
    tensorBimoduleObj ((pullback R f rfl).obj M) (pathChainBimodule B' a b R) ⟶
      (pullback R f (rfl : f b = f b)).obj
        (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R)) :=
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
    (fun hm c ↦ differential_changeBasepointPullbackBilin f M hm c)).val

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
@[simp]
theorem restrictScalarsEquiv_changeBasepointPullbackHom_tmul (m : (pullback R f rfl).obj M)
    (c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
        (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))
        (changeBasepointPullbackHom f M (tmul R (loopChainAlgebra B' a R) m c)) =
      tmul R (loopChainAlgebra B (f a) R) (restrictScalarsEquiv (loopChainMap R f rfl) M m)
        (cubicalChainModuleLinearMap (G' := MooreLoopSpace B (f b)) R
          (MoorePathBetween.map f) c) :=
  (congrArg _ (changeBasepointPullbackHom_tmul m c)).trans
    (restrictScalarsEquiv_changeBasepointPullbackBilin f M m c)

/-- The left side of `changeBasepointPullbackHom_naturality` on a pure tensor `m ⊗ c`, after
restriction: `e (φ_N (g m ⊗ c)) = g (e m) ⊗ f_* c`. -/
private theorem restrictScalarsEquiv_tensorBimoduleMap_comp_changeBasepointPullbackHom_tmul
    {N : DGLocalSystem.{v} B (f a) R} (g : M ⟶ N) (m : (pullback R f rfl).obj M)
    (c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
        (tensorBimoduleObj N (pathChainBimodule B (f a) (f b) R))
        ((tensorBimoduleMap ((pullback R f rfl).map g) (𝟙 (pathChainBimodule B' a b R)) ≫
          changeBasepointPullbackHom f N) (tmul R (loopChainAlgebra B' a R) m c)) =
      tmul R (loopChainAlgebra B (f a) R) (g (restrictScalarsEquiv (loopChainMap R f rfl) M m))
        (cubicalChainModuleLinearMap (G' := MooreLoopSpace B (f b)) R
          (MoorePathBetween.map f) c) := by
  rw [DGRightModuleCat.comp_apply, tensorBimoduleMap_tmul, DGBimoduleCat.id_apply,
    restrictScalarsEquiv_changeBasepointPullbackHom_tmul, restrictScalars_map_apply]

/-- The right side of `changeBasepointPullbackHom_naturality` on a pure tensor `m ⊗ c`, after
restriction: `e (f^* (g ⊗ 1) (φ_M (m ⊗ c))) = (g ⊗ 1) (e m ⊗ f_* c) = g (e m) ⊗ f_* c`. -/
private theorem restrictScalarsEquiv_changeBasepointPullbackHom_comp_map_tmul
    {N : DGLocalSystem.{v} B (f a) R} (g : M ⟶ N) (m : (pullback R f rfl).obj M)
    (c : cubicalChainModule (MoorePathBetween B' a b) (MooreLoopSpace B' b) R) :
    restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
        (tensorBimoduleObj N (pathChainBimodule B (f a) (f b) R))
        ((changeBasepointPullbackHom f M ≫ (pullback R f (rfl : f b = f b)).map
          (tensorBimoduleMap g (𝟙 (pathChainBimodule B (f a) (f b) R))))
            (tmul R (loopChainAlgebra B' a R) m c)) =
      tmul R (loopChainAlgebra B (f a) R) (g (restrictScalarsEquiv (loopChainMap R f rfl) M m))
        (cubicalChainModuleLinearMap (G' := MooreLoopSpace B (f b)) R
          (MoorePathBetween.map f) c) := by
  rw [DGRightModuleCat.comp_apply, restrictScalars_map_apply,
    restrictScalarsEquiv_changeBasepointPullbackHom_tmul, tensorBimoduleMap_tmul,
    DGBimoduleCat.id_apply]

variable (f M) in
/-- `changeBasepointPullbackHom` is natural in the DG local system. -/
theorem changeBasepointPullbackHom_naturality {N : DGLocalSystem.{v} B (f a) R} (g : M ⟶ N) :
    tensorBimoduleMap ((pullback R f rfl).map g) (𝟙 (pathChainBimodule B' a b R)) ≫
        changeBasepointPullbackHom f N =
      changeBasepointPullbackHom f M ≫
        (pullback R f (rfl : f b = f b)).map
          (tensorBimoduleMap g (𝟙 (pathChainBimodule B (f a) (f b) R))) := by
  refine hom_ext fun z ↦ ?_
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => rw [map_add, map_add, hz, hz']
  | ht m c =>
    -- Writing `e` for the restriction equivalences, both sides are computed to `g (e m) ⊗ f_* c`
    -- in separate lemmas: computing them in one proof is close to the heartbeat limit.
    exact (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
      (tensorBimoduleObj N (pathChainBimodule B (f a) (f b) R))).injective
      ((restrictScalarsEquiv_tensorBimoduleMap_comp_changeBasepointPullbackHom_tmul g m c).trans
        (restrictScalarsEquiv_changeBasepointPullbackHom_comp_map_tmul g m c).symm)

variable (R f a b) in
/-- **Changing the basepoint commutes with pullback**, as a natural transformation
`f^*(-) ⊗ C_*(P_{a→b} B') ⟶ f^*((-) ⊗ C_*(P_{f a→f b} B))` with components
`TauCeti.DGLocalSystem.changeBasepointPullbackHom`. -/
def changeBasepointPullback :
    pullback.{v} R f (rfl : f a = f a) ⋙ basepointChange R a b ⟶
      basepointChange R (f a) (f b) ⋙ pullback R f (rfl : f b = f b) where
  app M := changeBasepointPullbackHom f M
  naturality _ _ g := changeBasepointPullbackHom_naturality f _ g

@[simp]
theorem changeBasepointPullback_app :
    (changeBasepointPullback R f a b).app M = changeBasepointPullbackHom f M :=
  (rfl)

/-- `changeBasepointPullbackHom` is compatible with the retractions `m ⊗ c ↦ m · ρ(c)` of both
sides onto `M`, through a path `δ` and its image. -/
private theorem tensorPathChainAct_changeBasepointPullbackHom (δ : MoorePathBetween B' a b)
    (x : tensorBimoduleObj ((pullback R f rfl).obj M) (pathChainBimodule B' a b R)) :
    tensorPathChainAct M (MoorePathBetween.map f δ)
        (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
          (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))
          (changeBasepointPullbackHom f M x)) =
      restrictScalarsEquiv (loopChainMap R f rfl) M
        (tensorPathChainAct ((pullback R f rfl).obj M) δ x) := by
  induction x using BalancedTensorProduct.induction_on with
  | ha x x' hx hx' => simp only [map_add, hx, hx']
  | ht m c =>
    -- Both sides are `m · ρ(f_* c)`, where `ρ` appends the reversal of `f ∘ δ`: on the left after
    -- computing `e (φ (m ⊗ c)) = m ⊗ f_* c`, on the right by `ρ_{f ∘ δ} ∘ f_* = C_*(Ωf) ∘ ρ_δ`
    -- (`pathChainToLoopChain_cubicalChainModuleLinearMap`) and the restricted action.
    rw [restrictScalarsEquiv_changeBasepointPullbackHom_tmul, tensorPathChainAct_tmul,
      pathChainToLoopChain_cubicalChainModuleLinearMap, tensorPathChainAct_tmul,
      restrictScalarsEquiv_smul, unop_op]

/-- `changeBasepointPullbackHom` is compatible with the sections `m ↦ m ⊗ [δ]` of both sides,
through a path `δ` and its image. -/
private theorem changeBasepointPullbackHom_tensorPathChainPoint (δ : MoorePathBetween B' a b)
    (m : M) :
    changeBasepointPullbackHom f M (tensorPathChainPoint ((pullback R f rfl).obj M) δ
        ((restrictScalarsEquiv (loopChainMap R f rfl) M).symm m)) =
      (restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
          (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).symm
        (tensorPathChainPoint M (MoorePathBetween.map f δ) m) :=
  -- Both sides are `m ⊗ [f ∘ δ]` after restriction: on the left `e (φ (e⁻¹ m ⊗ [δ])) = m ⊗ f_* [δ]`
  -- and `f_* [δ] = [f ∘ δ]` (`cubicalChainModuleLinearMap_pathChainPoint`). The first two steps
  -- are terms: rewriting with them is close to the heartbeat limit.
  (LinearEquiv.eq_symm_apply _).mpr <|
    (congrArg (fun x ↦ restrictScalarsEquiv (loopChainMap R f (rfl : f b = f b))
      (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R)) (changeBasepointPullbackHom f M x))
      (tensorPathChainPoint_apply _ δ _)).trans <|
    (restrictScalarsEquiv_changeBasepointPullbackHom_tmul _ _).trans <| by
      rw [LinearEquiv.apply_symm_apply, cubicalChainModuleLinearMap_pathChainPoint,
        tensorPathChainPoint_apply]

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
  let := (tensorBimoduleObj N (pathChainBimodule B' a b R)).moduleOp
  let := (tensorBimoduleObj N (pathChainBimodule B' a b R)).scalarTower
  let := (tensorBimoduleObj N (pathChainBimodule B' a b R)).gradedSMul
  let := ((pullback R f (rfl : f b = f b)).obj
    (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R))).gradedSMul
  -- The target is the restriction of `M ⊗ C_*(P_{f a→f b} B)`, a homotopy retract of `M`
  -- through `f ∘ δ`; restriction carries this retract data along `e'`.
  obtain ⟨hiN, hrN, hKN⟩ := restrictScalars_homotopyRetract (loopChainMap R f (rfl : f b = f b))
    (tensorBimoduleObj M (pathChainBimodule B (f a) (f b) R)) (differential_tensorPathChainAct δ')
    (differential_tensorPathChainPoint δ') (tensorPathChainPoint_tensorPathChainAct δ')
  -- The source `N ⊗ C_*(P_{a→b} B')` is a homotopy retract of `N`, hence of `M` through `e`.
  refine DGRightModuleHom.isQuasiIso_of_homotopyRetract (changeBasepointPullbackHom f M)
    (dM₀ := M.differential) (dN₀ := M.differential) LinearMap.id
    (fun x y _ hxy ↦ ⟨y, 0, hxy.symm, by rw [map_zero, add_zero, LinearMap.id_apply]⟩)
    (e.toLinearMap ∘ₗ tensorPathChainAct N δ) (tensorPathChainPoint N δ ∘ₗ e.symm.toLinearMap)
    (tensorPathChainHomotopy N δ)
    (tensorPathChainAct M δ' ∘ₗ e'.toLinearMap) (e'.symm.toLinearMap ∘ₗ tensorPathChainPoint M δ')
    (e'.symm.toLinearMap ∘ₗ tensorPathChainHomotopy M δ' ∘ₗ e'.toLinearMap)
    (fun x ↦ ?_) (fun x ↦ ?_) hiN hrN (fun x ↦ ?_) hKN
    (tensorPathChainAct_changeBasepointPullbackHom δ)
    (changeBasepointPullbackHom_tensorPathChainPoint δ)
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ← differential_tensorPathChainAct, restrictScalarsEquiv_differential]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      differential_tensorPathChainPoint, restrictScalarsEquiv_symm_differential]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact tensorPathChainPoint_tensorPathChainAct δ x

end DGLocalSystem

end TauCeti

end
