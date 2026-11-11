/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Bimodule
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Homotopy
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Module
public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso
public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Differential

/-!
# Changing the basepoint of a DG local system preserves quasi-isomorphisms

For points `a` and `b` of a space `B`, a DG local system at `a`, that is a right DG module `M`
over the chain algebra `C_*(Ω_a B)`, becomes one at `b` by tensoring with the chain bimodule
`C_*(P_{a→b} B)` of Moore paths from `a` to `b`. This file shows that when `a` and `b` are joined
by a path, this ordinary tensor product preserves quasi-isomorphisms
(`TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule`). So basepoint change needs no
resolution of the local system: the ordinary tensor product already computes the derived one.

The reason is that `C_*(P_{a→b} B)` is a homotopy retract of the free module of rank one as a
**left** module over `C_*(Ω_a B)`. Fix a Moore path `δ` from `a` to `b`. Appending its reversal,
`P_{a→b} B → Ω_a B`, commutes with the loops at `a` acting in front, so on chains it is a map
`ρ` of left modules into `C_*(Ω_a B)` (`TauCeti.pathChainToLoopChain_smul`). Acting on the
`0`-chain `[δ]` of `δ` goes back, and the composite `c ↦ ρ(c) · [δ]` is the push-forward of
appending `δ⁻¹` and then `δ` (`TauCeti.pathChainToLoopChain_smul_pathChainPoint`), which the
growing retracing suffix joins to the identity through a homotopy that is graded linear for the
left action (`TauCeti.pathChainAppendHomotopy`). Tensoring with a right module `M` gives the maps
`m ⊗ c ↦ m · ρ(c)` from `M ⊗ C_*(P_{a→b} B)` to `M` and `m ↦ m ⊗ [δ]` back, and the homotopy
`m ⊗ c ↦ (-1) ^ |m| m ⊗ K c` between their composite and the identity. These maps are not linear
over the loops at `b`, but they are natural in `M`, which is all that is needed to transfer
quasi-isomorphisms (`TauCeti.DGRightModuleCat.isQuasiIso_of_homotopyRetract`).

## Main definitions

* `TauCeti.pathChainToLoopChain`: appending the reversal of `δ`, on chains.
* `TauCeti.tensorPathChainRetract`, `TauCeti.tensorPathChainPoint`,
  `TauCeti.tensorPathChainHomotopy`: the retraction of `M ⊗ C_*(P_{a→b} B)` onto `M`, the map back
  and the homotopy between their composite and the identity.

## Main results

* `TauCeti.pathChainToLoopChain_smul`: `ρ` is a map of left modules over `C_*(Ω_a B)`.
* `TauCeti.pathChainToLoopChain_smul_pathChainPoint`: `ρ(c) · [δ]` is the push-forward of
  appending `δ⁻¹` and then `δ`.
* `TauCeti.tensorPathChainPoint_tensorPathChainRetract`: the composite of the retraction and the
  map back is homotopic to the identity.
* `TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule`: basepoint change along a path
  preserves quasi-isomorphisms.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.
-/

public noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe u w v

variable {B : Type u} [TopologicalSpace B] (R : Type w) [CommRing R] {a b : B}

/-- The map `ρ : C_*(P_{a→b} B) → C_*(Ω_a B)` of chains induced by appending the reversal of a
Moore path `δ` from `a` to `b`. -/
def pathChainToLoopChain (δ : MoorePathBetween B a b) :
    cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R →ₗ[R]
      loopChainAlgebra B a R :=
  cubicalChainSumMap R (MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun ∘ₗ
    (cubicalChainModuleEquiv _ _ R).toLinearMap

variable {R}

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

/-- `pathChainToLoopChain` commutes with the differentials. -/
theorem pathChainToLoopChain_differential (δ : MoorePathBetween B a b)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    pathChainToLoopChain R δ (cubicalChainModuleDifferential _ _ R x) =
      cubicalChainDifferential (MooreLoopSpace B a) R (pathChainToLoopChain R δ x) := by
  simp only [pathChainToLoopChain, LinearMap.comp_apply, LinearEquiv.coe_coe,
    cubicalChainModuleEquiv_differential, cubicalChainDifferential_cubicalChainSumMap]

variable (R) in
/-- The `0`-chain of a path. -/
def pathChainPoint (δ : MoorePathBetween B a b) :
    cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R :=
  cubicalChainModuleLof _ _ R 0 (NormalizedCubicalChain.ofCube _ R (SingularCube.point δ))

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
    induction c using NormalizedCubicalChain.induction_on with
    | zero => simp
    | add c c' hc hc' => simp only [map_add, add_smul, hc, hc']
    | smul r c hc => simp only [map_smul, smul_assoc, hc]
    | ofCube c =>
      rw [pathChainToLoopChain_lof, pathChainPoint, lof_smul_cubicalChainModuleLof,
        cubicalChainModuleLinearMap_lof, NormalizedCubicalChain.map_ofCube,
        NormalizedCubicalChain.map_ofCube, NormalizedCubicalChain.leftAct_ofCube,
        ← cubicalChainModuleLof_cast (Nat.add_zero q), NormalizedCubicalChain.ofCube_def,
        NormalizedCubicalChain.cast_mk, CubicalChain.cast_single,
        ← NormalizedCubicalChain.ofCube_def]
      congr 2
      refine ContinuousMap.ext fun x ↦ ?_
      have hx : (fun i : Fin q ↦ x (Fin.cast (Nat.add_zero q) (Fin.castAdd 0 i))) = x :=
        funext fun i ↦ congrArg x (Fin.ext (by simp))
      simp only [SingularCube.cast_apply, ContinuousMap.comp_apply,
        SingularCube.crossProduct_apply, Function.comp_apply, hx, leftActMap_apply,
        SingularCube.point_apply]
      apply MoorePathBetween.ext
      simp [MoorePath.trans_assoc]

section BasepointChange

open BalancedTensorProduct DGRightModuleCat

variable (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))
  (δ : MoorePathBetween B a b)

/-- The retraction `M ⊗ C_*(P_{a→b} B) → M`, `m ⊗ c ↦ m · ρ(c)`, where `ρ` appends the reversal
of `δ`. -/
def tensorPathChainRetract : tensorBimoduleObj M (pathChainBimodule B a b R) →ₗ[R] M :=
  lift (LinearMap.mk₂ R (fun m c ↦ op (pathChainToLoopChain R δ c) • m)
      (fun _ _ _ ↦ smul_add _ _ _) (fun r m c ↦ smul_comm _ r m)
      (fun m c c' ↦ by rw [map_add, MulOpposite.op_add, add_smul])
      (fun r m c ↦ by rw [map_smul, op_smul, smul_assoc]))
    (fun α m c ↦ by
      simp only [LinearMap.mk₂_apply, pathChainToLoopChain_smul, op_mul, mul_smul])

/-- On pure tensors the retraction is `m ⊗ c ↦ m · ρ(c)`. -/
@[simp]
theorem tensorPathChainRetract_tmul (m : M)
    (c : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    tensorPathChainRetract M δ (tmul R (loopChainAlgebra B a R) m c) =
      op (pathChainToLoopChain R δ c) • m :=
  lift_tmul _ _ m c

-- Instance search finds a different, but definitionally equal, decomposition of the loop chain
-- algebra than the one recorded in a DG module over it.
local instance (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)) :
    SetLike.GradedSMul
      (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B a) R)).opposite.piece
      M.grading :=
  M.gradedSMul

/-- The map `M → M ⊗ C_*(P_{a→b} B)`, `m ↦ m ⊗ [δ]`, tensoring with the `0`-chain of `δ`. -/
def tensorPathChainPoint : M →ₗ[R] tensorBimoduleObj M (pathChainBimodule B a b R) :=
  (BalancedTensorProduct.mk R (loopChainAlgebra B a R)).flip (pathChainPoint R δ)

/-- The map back is `m ↦ m ⊗ [δ]`. -/
@[simp]
theorem tensorPathChainPoint_apply (m : M) :
    tensorPathChainPoint M δ m = tmul R (loopChainAlgebra B a R) m (pathChainPoint R δ) := by
  rw [tensorPathChainPoint, LinearMap.flip_apply, mk_apply]

variable {M}

/-- The retraction commutes with the differentials. -/
theorem differential_tensorPathChainRetract
    (z : tensorBimoduleObj M (pathChainBimodule B a b R)) :
    M.differential (tensorPathChainRetract M δ z) =
      tensorPathChainRetract M δ
        ((tensorBimoduleObj M (pathChainBimodule B a b R)).differential z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => simp only [map_add, hz, hz']
  | ht m c =>
    induction m using DirectSum.Decomposition.inductionOn M.grading with
    | zero => simp [zero_tmul]
    | add m m' hm hm' => rw [add_tmul, map_add, map_add, hm, hm', map_add, map_add]
    | @homogeneous q m =>
      rw [tensorPathChainRetract_tmul, M.isDGRightModule.leibniz m.2,
        tensorBimoduleObj_differential_tmul m.2, map_add, map_zsmul_unit,
        tensorPathChainRetract_tmul, tensorPathChainRetract_tmul]
      rw [← pathChainToLoopChain_differential]

/-- Tensoring with the `0`-chain of `δ` commutes with the differentials. -/
theorem differential_tensorPathChainPoint (m : M) :
    (tensorBimoduleObj M (pathChainBimodule B a b R)).differential (tensorPathChainPoint M δ m) =
      tensorPathChainPoint M δ (M.differential m) := by
  induction m using DirectSum.Decomposition.inductionOn M.grading with
  | zero => simp
  | add m m' hm hm' => simp only [map_add, hm, hm']
  | @homogeneous q m =>
    rw [tensorPathChainPoint_apply, tensorBimoduleObj_differential_tmul m.2,
      tensorPathChainPoint_apply]
    have h0 : (pathChainBimodule B a b R).differential (pathChainPoint R δ) = 0 :=
      cubicalChainModuleDifferential_lof_zero _
    rw [h0, tmul_zero, smul_zero, add_zero]

variable (M) in
/-- The chain homotopy `m ⊗ c ↦ (-1) ^ |m| m ⊗ K c` on `M ⊗ C_*(P_{a→b} B)`, for the homotopy
`K = pathChainAppendHomotopy R δ` growing the retracing suffix. -/
def tensorPathChainHomotopy : tensorBimoduleObj M (pathChainBimodule B a b R) →ₗ[R]
    tensorBimoduleObj M (pathChainBimodule B a b R) :=
  koszulMapRight M.grading (fun hα x ↦ pathChainAppendHomotopy_smul δ hα x)

/-- On a homogeneous first factor of degree `q`, the homotopy carries the sign `(-1) ^ q`. -/
theorem tensorPathChainHomotopy_tmul_of_mem {q : ℤ} {m : M} (hm : m ∈ M.grading q)
    (c : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    tensorPathChainHomotopy M δ (tmul R (loopChainAlgebra B a R) m c) =
      ((q.negOnePow : ℤ) : R) •
        tmul R (loopChainAlgebra B a R) m (pathChainAppendHomotopy R δ c) :=
  koszulMapRight_tmul_of_mem _ hm c

/-- **`M` is a homotopy retract of `M ⊗ C_*(P_{a→b} B)`**: following the retraction by
`m ↦ m ⊗ [δ]` is homotopic to the identity, through `tensorPathChainHomotopy M δ`. -/
theorem tensorPathChainPoint_tensorPathChainRetract
    (z : tensorBimoduleObj M (pathChainBimodule B a b R)) :
    tensorPathChainPoint M δ (tensorPathChainRetract M δ z) =
      z + (tensorBimoduleObj M (pathChainBimodule B a b R)).differential
          (tensorPathChainHomotopy M δ z) +
        tensorPathChainHomotopy M δ
          ((tensorBimoduleObj M (pathChainBimodule B a b R)).differential z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' =>
    simp only [map_add, hz, hz']
    abel
  | ht m c =>
    have h := tmul_sub_tmul_eq_add_koszulMapRight (ℳ := M.grading)
      (N := (pathChainBimodule B a b R).carrier) (N' := (pathChainBimodule B a b R).carrier)
      (dN := (pathChainBimodule B a b R).differential)
      (dN' := (pathChainBimodule B a b R).differential)
      (D := (tensorBimoduleObj M (pathChainBimodule B a b R)).differential)
      (D' := (tensorBimoduleObj M (pathChainBimodule B a b R)).differential)
      M.isDGRightModule.isHomogeneous
      (fun hα x ↦ pathChainAppendHomotopy_smul δ hα x)
      (g₁ := cubicalChainModuleLinearMap R
        ((MoorePathBetween.append δ a).comp (MoorePathBetween.append δ.symm a)))
      (g₂ := LinearMap.id) (fun x ↦ (pathChainAppendHomotopy_spec δ x).symm)
      (fun hm x ↦ tensorBimoduleObj_differential_tmul hm x)
      (fun hm x ↦ tensorBimoduleObj_differential_tmul hm x) m c
    rw [LinearMap.id_apply, sub_eq_iff_eq_add'] at h
    rw [tensorPathChainRetract_tmul, tensorPathChainPoint_apply, balance,
      pathChainToLoopChain_smul_pathChainPoint, h, add_assoc]
    -- `tensorPathChainHomotopy M δ` is `koszulMapRight` by definition.
    rfl

variable {δ}

/-- **Changing the basepoint along Moore paths preserves quasi-isomorphisms.** If `a` and `b`
are joined by a Moore path, then for every quasi-isomorphism `f : M → N` of DG local systems at
`a`, the tensored morphism `f ⊗ 1 : M ⊗ C_*(P_{a→b} B) → N ⊗ C_*(P_{a→b} B)` of DG local
systems at `b` is a quasi-isomorphism. So the ordinary tensor product with the path bimodule
already computes the derived one. -/
theorem isQuasiIso_tensorBimoduleMap_pathChainBimodule [Nonempty (MoorePathBetween B a b)]
    {M N : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)} {f : M ⟶ N}
    (hf : IsQuasiIso f) : IsQuasiIso (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R))) := by
  obtain ⟨δ⟩ := ‹Nonempty (MoorePathBetween B a b)›
  -- Additivity of the tensored morphism, stated for arbitrary objects: instance search does not
  -- see the module structures of the tensor product through its carrier.
  have hF0 {X Y : DGRightModuleCat.{w, max u w, max v u w} (loopChain_isDGAlgebra B b R)}
      (F : X ⟶ Y) : F 0 = 0 := map_zero F
  have hFadd {X Y : DGRightModuleCat.{w, max u w, max v u w} (loopChain_isDGAlgebra B b R)}
      (F : X ⟶ Y) (z z' : X) : F (z + z') = F z + F z' := map_add F z z'
  have hFz {X Y : DGRightModuleCat.{w, max u w, max v u w} (loopChain_isDGAlgebra B b R)}
      (F : X ⟶ Y) (n : ℤ) (z : X) : F (n • z) = n • F z := map_zsmul F n z
  refine isQuasiIso_of_homotopyRetract
    (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R))) (f.toLinearMap.restrictScalars R)
    ((DGRightModuleHom.isQuasiIso_iff_forall_exists f).1 hf)
    (tensorPathChainRetract M δ) (tensorPathChainPoint M δ) (tensorPathChainHomotopy M δ)
    (tensorPathChainRetract N δ) (tensorPathChainPoint N δ) (tensorPathChainHomotopy N δ)
    (differential_tensorPathChainRetract δ) (differential_tensorPathChainPoint δ)
    (differential_tensorPathChainRetract δ) (differential_tensorPathChainPoint δ)
    (tensorPathChainPoint_tensorPathChainRetract δ)
    (tensorPathChainPoint_tensorPathChainRetract δ) (fun z ↦ ?_) (fun m ↦ ?_) (fun z ↦ ?_)
  · induction z using BalancedTensorProduct.induction_on with
    | ha z z' hz hz' => simp only [map_add, hz, hz']
    | ht m c =>
      rw [tensorBimoduleMap_tmul, tensorPathChainRetract_tmul, tensorPathChainRetract_tmul,
        DGBimoduleCat.id_apply, LinearMap.restrictScalars_apply,
        DGRightModuleHom.coe_toLinearMap]
      exact (map_smul f _ m).symm
  · rw [tensorPathChainPoint_apply, tensorPathChainPoint_apply, tensorBimoduleMap_tmul,
      DGBimoduleCat.id_apply, LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap]
  · induction z using BalancedTensorProduct.induction_on with
    | ha z z' hz hz' => rw [map_add, hFadd, hFadd, map_add, hz, hz']
    | ht m c =>
      induction m using DirectSum.Decomposition.inductionOn M.grading with
      | zero => rw [zero_tmul, map_zero, hF0, map_zero]
      | add m m' hm hm' => rw [add_tmul, map_add, hFadd, hm, hm', ← map_add, ← hFadd]
      | @homogeneous q m =>
        rw [tensorPathChainHomotopy_tmul_of_mem δ m.2, Int.cast_smul_eq_zsmul, hFz,
          tensorBimoduleMap_tmul, tensorBimoduleMap_tmul,
          tensorPathChainHomotopy_tmul_of_mem δ (GradedFunLike.map_mem f m.2),
          Int.cast_smul_eq_zsmul, DGBimoduleCat.id_apply, DGBimoduleCat.id_apply]

end BasepointChange

end TauCeti
