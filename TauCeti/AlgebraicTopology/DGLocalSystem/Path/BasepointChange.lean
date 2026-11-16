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
`C_*(P_{a→b} B)` of Moore paths from `a` to `b`. This file shows that this ordinary tensor product
preserves quasi-isomorphisms (`TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule`). So
basepoint change needs no resolution of the local system: the ordinary tensor product already
computes the derived one.

When no Moore path joins `a` to `b`, the path chains vanish and there is nothing to prove.
Otherwise, `C_*(P_{a→b} B)` is a homotopy retract of the free module of rank one as a
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
quasi-isomorphisms (`TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyRetract`).

## Main definitions

* `TauCeti.pathChainToLoopChain`: appending the reversal of `δ`, on chains.
* `TauCeti.tensorPathChainAct`, `TauCeti.tensorPathChainPoint`,
  `TauCeti.tensorPathChainHomotopy`: the map `m ⊗ c ↦ m · ρ(c)` from `M ⊗ C_*(P_{a→b} B)` to `M`,
  the map `m ↦ m ⊗ [δ]` back and the homotopy between their composite and the identity, which
  make `M ⊗ C_*(P_{a→b} B)` a homotopy retract of `M`.

## Main results

* `TauCeti.pathChainToLoopChain_smul`: `ρ` is a map of left modules over `C_*(Ω_a B)`.
* `TauCeti.pathChainToLoopChain_smul_pathChainPoint`: `ρ(c) · [δ]` is the push-forward of
  appending `δ⁻¹` and then `δ`.
* `TauCeti.tensorPathChainPoint_tensorPathChainAct`: the composite of `m ⊗ c ↦ m · ρ(c)` and
  the map back is homotopic to the identity.
* `TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule`: basepoint change preserves
  quasi-isomorphisms.

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

section BasepointChange

open BalancedTensorProduct DGRightModuleCat

-- Instance search finds a different, but definitionally equal, decomposition of the loop chain
-- algebra than the one recorded in a DG module over it.
local instance (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)) :
    SetLike.GradedSMul
      (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B a) R)).opposite.piece
      M.grading :=
  M.gradedSMul

variable (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))
  (δ : MoorePathBetween B a b)

/-- The map `M ⊗ C_*(P_{a→b} B) → M`, `m ⊗ c ↦ m · ρ(c)`, where `ρ` appends the reversal of `δ`:
tensoring `ρ` with `M`, followed by the right action. It is the inclusion of the homotopy retract
`M ⊗ C_*(P_{a→b} B)` into `M`, with `tensorPathChainPoint` as the retraction back. -/
def tensorPathChainAct : tensorBimoduleObj M (pathChainBimodule B a b R) →ₗ[R] M :=
  (rid R (loopChainAlgebra B a R) M).toLinearMap ∘ₗ
    map LinearMap.id (pathChainToLoopChain R δ) (fun _ _ ↦ rfl) (pathChainToLoopChain_smul δ)

/-- On pure tensors the map is `m ⊗ c ↦ m · ρ(c)`. -/
@[simp]
theorem tensorPathChainAct_tmul (m : M)
    (c : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    tensorPathChainAct M δ (tmul R (loopChainAlgebra B a R) m c) =
      op (pathChainToLoopChain R δ c) • m := by
  rw [tensorPathChainAct, LinearMap.comp_apply, map_tmul, LinearEquiv.coe_coe, rid_tmul,
    LinearMap.id_apply]

/-- The map `M → M ⊗ C_*(P_{a→b} B)`, `m ↦ m ⊗ [δ]`, tensoring with the `0`-chain of `δ`. -/
def tensorPathChainPoint : M →ₗ[R] tensorBimoduleObj M (pathChainBimodule B a b R) :=
  (BalancedTensorProduct.mk R (loopChainAlgebra B a R)).flip (pathChainPoint R δ)

/-- The map back is `m ↦ m ⊗ [δ]`. -/
@[simp]
theorem tensorPathChainPoint_apply (m : M) :
    tensorPathChainPoint M δ m = tmul R (loopChainAlgebra B a R) m (pathChainPoint R δ) := by
  rw [tensorPathChainPoint, LinearMap.flip_apply, mk_apply]

variable {M}

/-- The map `m ⊗ c ↦ m · ρ(c)` commutes with the differentials. -/
theorem differential_tensorPathChainAct
    (z : tensorBimoduleObj M (pathChainBimodule B a b R)) :
    M.differential (tensorPathChainAct M δ z) =
      tensorPathChainAct M δ
        ((tensorBimoduleObj M (pathChainBimodule B a b R)).differential z) := by
  have h := LinearMap.congr_fun
    (rid_comp_differential (loopChain_isDGAlgebra B a R) M.isDGRightModule)
    (map LinearMap.id (pathChainToLoopChain R δ) (fun _ _ ↦ rfl) (pathChainToLoopChain_smul δ) z)
  have h' := LinearMap.congr_fun (differential_naturality M.isDGRightModule
    (pathChainBimodule B a b R).isDGLeftModule M.isDGRightModule
    (loopChain_isDGAlgebra B a R).isDGLeftModule LinearMap.id (pathChainToLoopChain R δ)
    (fun _ _ ↦ rfl) (pathChainToLoopChain_smul δ) (LinearMap.isHomogeneous_id _) rfl
    (LinearMap.ext fun x ↦ (pathChainToLoopChain_differential δ x).symm)) z
  simp only [LinearMap.comp_apply] at h h'
  rw [tensorPathChainAct, LinearMap.comp_apply, LinearMap.comp_apply, ← h, h']

/-- Tensoring with the `0`-chain of `δ` commutes with the differentials. -/
theorem differential_tensorPathChainPoint (m : M) :
    (tensorBimoduleObj M (pathChainBimodule B a b R)).differential (tensorPathChainPoint M δ m) =
      tensorPathChainPoint M δ (M.differential m) := by
  rw [tensorPathChainPoint_apply, BalancedTensorProduct.differential_tmul,
    cubicalChainModuleDifferential_pathChainPoint, tmul_zero, add_zero, tensorPathChainPoint_apply]

/-- The map `m ⊗ c ↦ m · ρ(c)` is natural in `M`. -/
theorem tensorPathChainAct_tensorBimoduleMap
    {N : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)} (f : M ⟶ N)
    (z : tensorBimoduleObj M (pathChainBimodule B a b R)) :
    tensorPathChainAct N δ (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R)) z) =
      f (tensorPathChainAct M δ z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => simp only [map_add, hz, hz']
  | ht m c =>
    rw [tensorBimoduleMap_tmul, tensorPathChainAct_tmul, tensorPathChainAct_tmul,
      DGBimoduleCat.id_apply]
    exact (map_smul f _ m).symm

/-- Tensoring with the `0`-chain of `δ` is natural in `M`. -/
theorem tensorBimoduleMap_tensorPathChainPoint
    {N : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)} (f : M ⟶ N) (m : M) :
    tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R)) (tensorPathChainPoint M δ m) =
      tensorPathChainPoint N δ (f m) := by
  rw [tensorPathChainPoint_apply, tensorPathChainPoint_apply, tensorBimoduleMap_tmul,
    DGBimoduleCat.id_apply]

variable (M) in
/-- The chain homotopy `m ⊗ c ↦ (-1) ^ |m| m ⊗ K c` on `M ⊗ C_*(P_{a→b} B)`, for the homotopy
`K = pathChainAppendHomotopy R δ a` growing the retracing suffix. -/
def tensorPathChainHomotopy : tensorBimoduleObj M (pathChainBimodule B a b R) →ₗ[R]
    tensorBimoduleObj M (pathChainBimodule B a b R) :=
  koszulMapRight M.grading (fun hα x ↦ pathChainAppendHomotopy_smul δ a hα x)

/-- On pure tensors, the first factor acquires its Koszul twist. -/
@[simp]
theorem tensorPathChainHomotopy_tmul (m : M)
    (c : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    tensorPathChainHomotopy M δ (tmul R (loopChainAlgebra B a R) m c) =
      tmul R (loopChainAlgebra B a R) ((InternalGrading.ofDecomposition M.grading).koszulTwist 1 m)
        (pathChainAppendHomotopy R δ a c) :=
  koszulMapRight_tmul _ m c

/-- On a homogeneous first factor of degree `q`, the homotopy carries the sign `(-1) ^ q`. -/
theorem tensorPathChainHomotopy_tmul_of_mem {q : ℤ} {m : M} (hm : m ∈ M.grading q)
    (c : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    tensorPathChainHomotopy M δ (tmul R (loopChainAlgebra B a R) m c) =
      ((q.negOnePow : ℤ) : R) •
        tmul R (loopChainAlgebra B a R) m (pathChainAppendHomotopy R δ a c) :=
  koszulMapRight_tmul_of_mem _ hm c

/-- **`M ⊗ C_*(P_{a→b} B)` is a homotopy retract of `M`**: following `m ⊗ c ↦ m · ρ(c)` by
`m ↦ m ⊗ [δ]` is homotopic to the identity, through `tensorPathChainHomotopy M δ`. -/
theorem tensorPathChainPoint_tensorPathChainAct
    (z : tensorBimoduleObj M (pathChainBimodule B a b R)) :
    tensorPathChainPoint M δ (tensorPathChainAct M δ z) =
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
      (fun hα x ↦ pathChainAppendHomotopy_smul δ a hα x)
      (g₁ := cubicalChainModuleLinearMap R
        ((MoorePathBetween.append δ a).comp (MoorePathBetween.append δ.symm a)))
      (g₂ := LinearMap.id) (fun x ↦ (pathChainAppendHomotopy_spec δ a x).symm)
      (fun hm x ↦ tensorBimoduleObj_differential_tmul hm x)
      (fun hm x ↦ tensorBimoduleObj_differential_tmul hm x) m c
    rw [LinearMap.id_apply, sub_eq_iff_eq_add'] at h
    rw [tensorPathChainAct_tmul, tensorPathChainPoint_apply, balance,
      pathChainToLoopChain_smul_pathChainPoint, h, add_assoc, tensorPathChainHomotopy]

/-- **Changing the basepoint preserves quasi-isomorphisms.** For every quasi-isomorphism
`f : M → N` of DG local systems at `a`, the tensored morphism
`f ⊗ 1 : M ⊗ C_*(P_{a→b} B) → N ⊗ C_*(P_{a→b} B)` of DG local systems at `b` is a
quasi-isomorphism. So the ordinary tensor product with the path bimodule already computes the
derived one. -/
theorem isQuasiIso_tensorBimoduleMap_pathChainBimodule
    {M N : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)} {f : M ⟶ N}
    (hf : IsQuasiIso f) : IsQuasiIso (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R))) := by
  -- Instance search does not see the structures of a tensor product through its carrier.
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).moduleOp
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).scalarTower
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).gradedSMul
  let := (tensorBimoduleObj N (pathChainBimodule B a b R)).moduleOp
  let := (tensorBimoduleObj N (pathChainBimodule B a b R)).scalarTower
  let := (tensorBimoduleObj N (pathChainBimodule B a b R)).gradedSMul
  rcases isEmpty_or_nonempty (MoorePathBetween B a b) with hB | hB
  · -- Without Moore paths from `a` to `b`, there are no path chains, so both tensor products
    -- vanish.
    have hc (c : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) : c = 0 := by
      induction c using cubicalChainModule.induction_on with
      | add c c' ih ih' => rw [ih, ih', add_zero]
      | lof q c =>
        induction c using NormalizedCubicalChain.induction_on with
        | zero => exact map_zero _
        | add c c' ih ih' => rw [map_add, ih, ih', add_zero]
        | smul r c ih => rw [map_smul, ih, smul_zero]
        | ofCube c => exact isEmptyElim (c 0)
    have hz (L : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))
        (z : tensorBimoduleObj L (pathChainBimodule B a b R)) : z = 0 := by
      induction z using BalancedTensorProduct.induction_on with
      | ht m c => rw [hc c, tmul_zero]
      | ha z z' ih ih' => rw [ih, ih', add_zero]
    rw [IsQuasiIso, DGRightModuleHom.isQuasiIso_iff_forall_exists]
    exact fun x y _ _ ↦ ⟨0, 0, by rw [map_zero, hz M x],
      by rw [map_zero, map_zero, add_zero, hz N y]⟩
  · obtain ⟨δ⟩ := hB
    exact DGRightModuleHom.isQuasiIso_of_homotopyRetract
      (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R))) (f.toLinearMap.restrictScalars R)
      ((DGRightModuleHom.isQuasiIso_iff_forall_exists f).1 hf)
      (tensorPathChainAct M δ) (tensorPathChainPoint M δ) (tensorPathChainHomotopy M δ)
      (tensorPathChainAct N δ) (tensorPathChainPoint N δ) (tensorPathChainHomotopy N δ)
      (differential_tensorPathChainAct δ) (differential_tensorPathChainPoint δ)
      (differential_tensorPathChainAct δ) (differential_tensorPathChainPoint δ)
      (tensorPathChainPoint_tensorPathChainAct δ) (tensorPathChainPoint_tensorPathChainAct δ)
      (tensorPathChainAct_tensorBimoduleMap δ f) (tensorBimoduleMap_tensorPathChainPoint δ f)

end BasepointChange

end TauCeti
