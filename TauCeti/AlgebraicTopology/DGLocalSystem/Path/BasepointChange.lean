/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Bimodule
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Homotopy
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Module
public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso
public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Differential

/-!
# Changing the basepoint of a DG local system preserves and reflects quasi-isomorphisms

For points `a` and `b` of a space `B`, a DG local system at `a`, that is a right DG module `M`
over the chain algebra `C_*(Ω_a B)`, becomes one at `b` by tensoring with the chain bimodule
`C_*(P_{a→b} B)` of Moore paths from `a` to `b`. This file shows that this ordinary tensor product
preserves quasi-isomorphisms (`TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule`). So
basepoint change needs no resolution of the local system: the ordinary tensor product already
computes the derived one.

For preservation, when no Moore path joins `a` to `b`, the path chains vanish and there is nothing
to prove; reflection needs a Moore path from `a` to `b`, since without one `f ⊗ 1` is a map between
zero modules. Otherwise, `C_*(P_{a→b} B)` is a homotopy retract of the free module of rank one as a
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

The other composite, `m ↦ m · ρ([δ])`, is the right action of the `0`-chain of the loop
`δ ⋆ δ⁻¹`. That loop is joined to the unit in `Ω_a B`, so `ρ([δ])` differs from the unit by a
boundary `d h` (`TauCeti.exists_pathChainToLoopChain_pathChainPoint_eq_one_add`), and the right
action of `d h` is null-homotopic (`TauCeti.IsDGRightModule.op_map_smul_eq_add`). So `M` is also a
homotopy retract of `M ⊗ C_*(P_{a→b} B)`, naturally in `M`, and basepoint change along a path
reflects quasi-isomorphisms
(`TauCeti.isQuasiIso_of_isQuasiIso_tensorBimoduleMap_pathChainBimodule`).
Pushing path chains forward along a continuous map sends the `0`-chain of a path to that of its
image (`TauCeti.cubicalChainModuleLinearMap_pathChainPoint`) and intertwines the maps `ρ` of a path
and of its image (`TauCeti.pathChainToLoopChain_cubicalChainModuleLinearMap`).

The same two maps compare the chains on the paths from `a` to `b` with the chains on the loops at
`a`: `α ↦ α · [δ]` from `C_*(Ω_a B)` to `C_*(P_{a→b} B)` is linear for the loops at `a` acting in
front, and it is a quasi-isomorphism
(`TauCeti.exists_cubicalChainDifferential_eq_and_smul_pathChainPoint_add_eq`). This is the
computation over a zero-cell in Brown's model of the chains on the based path space of a CW complex.

## Main definitions

* `TauCeti.pathChainToLoopChain`: appending the reversal of `δ`, on chains.
* `TauCeti.DGLocalSystem.basepointChange R a b`: basepoint change from `a` to `b`, the functor
  `𝓕 ↦ 𝓕 ⊗_{C_*(Ω_a B)} C_*(P_{a→b} B)`.
* `TauCeti.tensorPathChainAct`, `TauCeti.tensorPathChainPoint`,
  `TauCeti.tensorPathChainHomotopy`: the map `m ⊗ c ↦ m · ρ(c)` from `M ⊗ C_*(P_{a→b} B)` to `M`,
  the map `m ↦ m ⊗ [δ]` back and the homotopy between their composite and the identity, which
  make `M ⊗ C_*(P_{a→b} B)` a homotopy retract of `M`.
* `TauCeti.DGLocalSystem.changeBasepoint R a b`: the functor `M ↦ M ⊗ C_*(P_{a→b} B)` from DG
  local systems at `a` to DG local systems at `b`.

## Main results

* `TauCeti.pathChainToLoopChain_smul`: `ρ` is a map of left modules over `C_*(Ω_a B)`.
* `TauCeti.pathChainToLoopChain_smul_pathChainPoint`: `ρ(c) · [δ]` is the push-forward of
  appending `δ⁻¹` and then `δ`.
* `TauCeti.exists_cubicalChainDifferential_eq_and_smul_pathChainPoint_add_eq`: appending `δ` is a
  quasi-isomorphism `C_*(Ω_a B) → C_*(P_{a→b} B)`, in the form of relative cycles and boundaries.
* `TauCeti.tensorPathChainPoint_tensorPathChainAct`: the composite of `m ⊗ c ↦ m · ρ(c)` and
  the map back is homotopic to the identity.
* `TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule`: basepoint change preserves
  quasi-isomorphisms.
* `TauCeti.exists_tensorPathChainAct_tensorPathChainPoint`: the composite of `m ↦ m ⊗ [δ]` and
  `m ⊗ c ↦ m · ρ(c)` is homotopic to the identity.
* `TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule_iff`,
  `TauCeti.DGLocalSystem.isQuasiIso_basepointChange_map_iff`: along a path, basepoint change
  preserves and reflects quasi-isomorphisms.

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

/-- `pathChainToLoopChain` is the push-forward along appending the reversal of `δ`, read in the
chain algebra of the loops at `a`. -/
theorem pathChainToLoopChain_apply (δ : MoorePathBetween B a b)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    pathChainToLoopChain R δ x =
      cubicalChainSumMap R (MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun
        (cubicalChainModuleEquiv _ _ R x) :=
  (rfl)

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
    rw [pathChainToLoopChain_lof, pathChainPoint_def, lof_smul_cubicalChainModuleLof,
      cubicalChainModuleLinearMap_lof, ← cubicalChainModuleLof_cast (Nat.add_zero q),
      NormalizedCubicalChain.leftAct_def, ← NormalizedCubicalChain.map_cast,
      NormalizedCubicalChain.crossProduct_point_right, ← h, NormalizedCubicalChain.map_comp,
      NormalizedCubicalChain.map_comp, LinearMap.comp_apply, LinearMap.comp_apply]

/-- **The `0`-chain of `δ ⋆ δ⁻¹` is homologous to the unit**: `ρ([δ])` differs from the unit
`[1]` of `C_*(Ω_a B)` by a boundary, the prism of the unit along a homotopy from appending `δ` and
then `δ⁻¹` to the identity of `Ω_a B`. -/
theorem exists_pathChainToLoopChain_pathChainPoint_eq_one_add (δ : MoorePathBetween B a b) :
    ∃ h : loopChainAlgebra B a R, pathChainToLoopChain R δ (pathChainPoint R δ) =
      1 + cubicalChainDifferential (MooreLoopSpace B a) R h := by
  obtain ⟨H⟩ := (MoorePathBetween.loopAppendHomotopyEquiv δ).left_inv
  refine ⟨-cubicalChainLof (MooreLoopSpace B a) R 1 (NormalizedCubicalChain.prism R H 0
    (NormalizedCubicalChain.ofCube _ R (SingularCube.point 1))), ?_⟩
  have hpt : ((MoorePathBetween.loopAppendHomotopyEquiv δ).invFun.comp
      (MoorePathBetween.loopAppendHomotopyEquiv δ).toFun).comp (SingularCube.point 1) =
      (MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun.comp (SingularCube.point δ) :=
    ContinuousMap.ext fun _ ↦ by
      simp [SingularCube.point_apply]
  rw [map_neg, cubicalChainDifferential_lof_succ, NormalizedCubicalChain.boundary_prism_zero]
  simp only [NormalizedCubicalChain.map_ofCube, hpt]
  simp [pathChainPoint_def, ← cubicalChainLof_one, NormalizedCubicalChain.one_def,
    NormalizedCubicalChain.map_ofCube]

/-- **Appending a path is a quasi-isomorphism of left modules**, on elements. For a Moore path `δ`
from `a` to `b`, the map `C_*(Ω_a B) → C_*(P_{a→b} B)`, `α ↦ α · [δ]`, which is linear for the
loops at `a` acting in front, has relative cycles that are relative boundaries: if `α` is a cycle
and `α · [δ] = d w`, then `α = d α'` and `α' · [δ] + d w' = w` for some `α'` and `w'`. -/
theorem exists_cubicalChainDifferential_eq_and_smul_pathChainPoint_add_eq
    (δ : MoorePathBetween B a b) {α : loopChainAlgebra B a R}
    {w : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R}
    (hα : cubicalChainDifferential (MooreLoopSpace B a) R α = 0)
    (hαw : α • pathChainPoint R δ = cubicalChainModuleDifferential _ _ R w) :
    ∃ (α' : loopChainAlgebra B a R)
      (w' : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R),
      cubicalChainDifferential (MooreLoopSpace B a) R α' = α ∧
        α' • pathChainPoint R δ + cubicalChainModuleDifferential _ _ R w' = w := by
  -- Appending the reversal of `δ` is a homotopy inverse: `ρ(α · [δ]) = α ρ([δ])` differs from `α`
  -- by the product of the cycle `α` with a boundary, and `ρ(w) · [δ]` is homotopic to `w`.
  set dM := cubicalChainModuleDifferential (MoorePathBetween B a b) (MooreLoopSpace B b) R
  set K := pathChainAppendHomotopy R δ a
  have hM := cubicalChainModule_isDGLeftModule (MooreLoopSpace B a) (MoorePathBetween B a b)
    (MooreLoopSpace B b) R
  -- Acting on the cycle `[δ]` commutes with the differentials.
  have hc (γ : loopChainAlgebra B a R) : dM (γ • pathChainPoint R δ) =
      cubicalChainDifferential (MooreLoopSpace B a) R γ • pathChainPoint R δ :=
    hM.leibniz_of_map_eq_zero γ (cubicalChainModuleDifferential_pathChainPoint δ)
  -- Appending `δ⁻¹` and then `δ` is homotopic to the identity through `K`.
  have hρc (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
      pathChainToLoopChain R δ x • pathChainPoint R δ = x + (dM (K x) + K (dM x)) := by
    rw [pathChainToLoopChain_smul_pathChainPoint, pathChainAppendHomotopy_spec, add_sub_cancel]
  -- `ρ([δ]) = 1 + d h`, and the cycle `α` times the boundary `d h` is a boundary `d β`.
  obtain ⟨h, hh⟩ := exists_pathChainToLoopChain_pathChainPoint_eq_one_add (R := R) δ
  obtain ⟨β, hβ⟩ := (loopChain_isDGAlgebra B a R).isDGLeftModule.smul_mem_range_of_map_eq_zero hα
    (LinearMap.mem_range_self (cubicalChainDifferential (MooreLoopSpace B a) R) h)
  -- So `α` bounds `α₀ = ρ(w) - β`.
  have hα₀ : cubicalChainDifferential (MooreLoopSpace B a) R (pathChainToLoopChain R δ w - β) =
      α := by
    rw [map_sub, ← pathChainToLoopChain_differential, ← hαw, pathChainToLoopChain_smul, hh,
      mul_add, mul_one, hβ, smul_eq_mul, add_sub_cancel_right]
  -- What `α₀ · [δ]` misses of `w`, corrected by `d (K w)`, is a cycle `z`.
  set z := w - (pathChainToLoopChain R δ w - β) • pathChainPoint R δ + dM (K w)
  have hz : dM z = 0 := by
    rw [map_add, map_sub, hc, hα₀, ← hαw, hM.sq_zero, sub_self, zero_add]
  have hzw : (pathChainToLoopChain R δ w - β) • pathChainPoint R δ + z = w + dM (K w) := by
    simp only [z]
    abel
  clear_value z
  -- Correct `α₀` by `ρ(z)`, which `z` is homologous to after acting on `[δ]`.
  refine ⟨pathChainToLoopChain R δ w - β + pathChainToLoopChain R δ z, -(K w + K z), ?_, ?_⟩
  · rw [map_add, hα₀, ← pathChainToLoopChain_differential, hz, map_zero, add_zero]
  · rw [add_smul, hρc, hz, map_zero, add_zero, map_neg, map_add dM, ← add_assoc, hzw]
    abel

section Map

variable {X : Type*} [TopologicalSpace X] (f : C(B, X))

/-- Pushing path chains forward along `f` sends the `0`-chain of a path to the `0`-chain of its
image. -/
@[simp]
theorem cubicalChainModuleLinearMap_pathChainPoint (δ : MoorePathBetween B a b) :
    cubicalChainModuleLinearMap R (MoorePathBetween.map f) (pathChainPoint R δ) =
      pathChainPoint R (MoorePathBetween.map f δ) := by
  rw [pathChainPoint_def, pathChainPoint_def, cubicalChainModuleLinearMap_lof,
    NormalizedCubicalChain.map_ofCube]
  congr 2
  exact ContinuousMap.ext fun t ↦ by simp only [ContinuousMap.comp_apply, SingularCube.point_apply]

/-- Appending the reversal of the image of `δ` after pushing path chains forward along `f` is
pushing loop chains forward along `f` after appending the reversal of `δ`. -/
theorem pathChainToLoopChain_cubicalChainModuleLinearMap (δ : MoorePathBetween B a b)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    pathChainToLoopChain R (MoorePathBetween.map f δ)
        (cubicalChainModuleLinearMap R (MoorePathBetween.map f) x) =
      loopChainMap R f rfl (pathChainToLoopChain R δ x) := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | lof q c =>
    have h : (MoorePathBetween.loopAppendHomotopyEquiv (MoorePathBetween.map f δ)).symm.toFun.comp
        (MoorePathBetween.map f) =
          (MooreLoopSpace.map f rfl).toContinuousMap.comp
            (MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun :=
      ContinuousMap.ext fun γ ↦ MooreLoopSpace.ext (by simp)
    rw [cubicalChainModuleLinearMap_lof, pathChainToLoopChain_lof, pathChainToLoopChain_lof,
      loopChainMap_lof, ← LinearMap.comp_apply (NormalizedCubicalChain.map R _ q),
      ← NormalizedCubicalChain.map_comp, h, NormalizedCubicalChain.map_comp, LinearMap.comp_apply]

end Map

section BasepointChange

open BalancedTensorProduct DGRightModuleCat

-- Transport the graded actions to the internal gradings used by balanced tensors.
local instance (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)) :
    SetLike.GradedSMul
      (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B a) R)).opposite.piece
      (InternalGrading.ofDecomposition M.grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  exact M.gradedSMul

local instance : SetLike.GradedSMul (cubicalChainGrading (MooreLoopSpace B a) R)
    (InternalGrading.ofDecomposition (pathChainBimodule B a b R).grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

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

/-- The map `m ⊗ c ↦ m · ρ(c)` preserves the degree. -/
theorem tensorPathChainAct_mem {q : ℤ} {z : tensorBimoduleObj M (pathChainBimodule B a b R)}
    (hz : z ∈ (tensorBimoduleObj M (pathChainBimodule B a b R)).grading q) :
    tensorPathChainAct M δ z ∈ M.grading q := by
  simpa only [add_zero] using map_mem_of_tmul (𝒜 := cubicalChainGrading (MooreLoopSpace B a) R)
    (InternalGrading.ofDecomposition M.grading)
    (InternalGrading.ofDecomposition (pathChainBimodule B a b R).grading) M.grading
    (tensorPathChainAct M δ) 0 (fun {p q m c} hm hc ↦ by
      rw [InternalGrading.ofDecomposition_piece] at hm hc
      have hρ := pathChainToLoopChain_mem δ hc
      rw [← InternalGrading.ofDecomposition_piece (cubicalChainGrading (MooreLoopSpace B a) R)]
        at hρ
      rw [tensorPathChainAct_tmul, add_zero, add_comm]
      exact SetLike.GradedSMul.smul_mem
        ((InternalGrading.op_mem_opposite_piece_iff _ _ _).2 hρ) hm) hz

/-- The map `m ↦ m ⊗ [δ]` preserves the degree. -/
theorem tensorPathChainPoint_mem {q : ℤ} {m : M} (hm : m ∈ M.grading q) :
    tensorPathChainPoint M δ m ∈ (tensorBimoduleObj M (pathChainBimodule B a b R)).grading q := by
  rw [tensorPathChainPoint_apply]
  simpa only [add_zero] using
    tmul_mem_tensorBimoduleObj_grading (N := pathChainBimodule B a b R) hm (pathChainPoint_mem δ)

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
  · -- Without Moore paths from `a` to `b`, both tensor products vanish.
    exact DGRightModuleHom.isQuasiIso_of_subsingleton _
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

variable (M) in
/-- **`M` is a homotopy retract of `M ⊗ C_*(P_{a→b} B)`**: following `m ↦ m ⊗ [δ]` by
`m ⊗ c ↦ m · ρ(c)` is the right action of `ρ([δ])`, the `0`-chain of `δ ⋆ δ⁻¹`, which is homotopic
to the identity since `ρ([δ])` differs from the unit by a boundary. -/
theorem exists_tensorPathChainAct_tensorPathChainPoint :
    ∃ K : M →ₗ[R] M, ∀ m, tensorPathChainAct M δ (tensorPathChainPoint M δ m) =
      m + M.differential (K m) + K (M.differential m) := by
  obtain ⟨h, hh⟩ := exists_pathChainToLoopChain_pathChainPoint_eq_one_add (R := R) δ
  refine ⟨DistribSMul.toLinearMap R M (op h) ∘ₗ
    (InternalGrading.ofDecomposition M.grading).koszulTwist 1, fun m ↦ ?_⟩
  rw [tensorPathChainPoint_apply, tensorPathChainAct_tmul, hh, MulOpposite.op_add, add_smul,
    op_one, one_smul, M.isDGRightModule.op_map_smul_eq_add h m, add_assoc]
  simp only [LinearMap.comp_apply, DistribSMul.toLinearMap_apply]

/-- **Changing the basepoint reflects quasi-isomorphisms.** If a Moore path joins `a` to `b`, a
morphism `f : M → N` of DG local systems at `a` is a quasi-isomorphism as soon as
`f ⊗ 1 : M ⊗ C_*(P_{a→b} B) → N ⊗ C_*(P_{a→b} B)` is one. -/
theorem isQuasiIso_of_isQuasiIso_tensorBimoduleMap_pathChainBimodule
    (hab : Nonempty (MoorePathBetween B a b))
    {M N : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)} {f : M ⟶ N}
    (hf : IsQuasiIso (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R)))) : IsQuasiIso f := by
  -- Instance search does not see the structures of a tensor product through its carrier.
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).moduleOp
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).scalarTower
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).gradedSMul
  let := (tensorBimoduleObj N (pathChainBimodule B a b R)).moduleOp
  let := (tensorBimoduleObj N (pathChainBimodule B a b R)).scalarTower
  let := (tensorBimoduleObj N (pathChainBimodule B a b R)).gradedSMul
  obtain ⟨δ⟩ := hab
  obtain ⟨KM, hKM⟩ := exists_tensorPathChainAct_tensorPathChainPoint M δ
  obtain ⟨KN, hKN⟩ := exists_tensorPathChainAct_tensorPathChainPoint N δ
  exact DGRightModuleHom.isQuasiIso_of_homotopyRetract f
    ((tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R))).toLinearMap.restrictScalars R)
    ((DGRightModuleHom.isQuasiIso_iff_forall_exists _).1 hf)
    (tensorPathChainPoint M δ) (tensorPathChainAct M δ) KM
    (tensorPathChainPoint N δ) (tensorPathChainAct N δ) KN
    (differential_tensorPathChainPoint δ) (differential_tensorPathChainAct δ)
    (differential_tensorPathChainPoint δ) (differential_tensorPathChainAct δ) hKM hKN
    (fun m ↦ (tensorBimoduleMap_tensorPathChainPoint δ f m).symm)
    (fun z ↦ (tensorPathChainAct_tensorBimoduleMap δ f z).symm)

/-- **Along a Moore path, changing the basepoint preserves and reflects quasi-isomorphisms**:
`f ⊗ 1` is a quasi-isomorphism exactly when `f` is. -/
theorem isQuasiIso_tensorBimoduleMap_pathChainBimodule_iff
    (hab : Nonempty (MoorePathBetween B a b))
    {M N : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)} {f : M ⟶ N} :
    IsQuasiIso (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R))) ↔ IsQuasiIso f :=
  ⟨isQuasiIso_of_isQuasiIso_tensorBimoduleMap_pathChainBimodule hab,
    isQuasiIso_tensorBimoduleMap_pathChainBimodule⟩

end BasepointChange

namespace DGLocalSystem

variable (R a b) in
/-- **Basepoint change** of DG local systems from `a` to `b`: the tensor product
`𝓕 ↦ 𝓕 ⊗_{C_*(Ω_a B)} C_*(P_{a→b} B)` with the chain bimodule of Moore paths from `a` to `b`. On
morphisms it is `φ ↦ φ ⊗ 1` (`TauCeti.DGLocalSystem.basepointChange_map`), so along a Moore path
it preserves and reflects quasi-isomorphisms
(`TauCeti.DGLocalSystem.isQuasiIso_basepointChange_map_iff`). -/
@[expose] def basepointChange : DGLocalSystem.{v} B a R ⥤ DGLocalSystem.{max v u w} B b R :=
  DGRightModuleCat.tensorBimoduleFunctor.flip.obj (pathChainBimodule B a b R)

/-- Basepoint change sends `𝓕` to `𝓕 ⊗_{C_*(Ω_a B)} C_*(P_{a→b} B)`. -/
@[simp]
theorem basepointChange_obj (M : DGLocalSystem.{v} B a R) :
    (basepointChange R a b).obj M =
      DGRightModuleCat.tensorBimoduleObj M (pathChainBimodule B a b R) :=
  (rfl)

/-- Basepoint change sends `φ` to `φ ⊗ 1`. -/
@[simp]
theorem basepointChange_map {M N : DGLocalSystem.{v} B a R} (φ : M ⟶ N) :
    (basepointChange R a b).map φ =
      DGRightModuleCat.tensorBimoduleMap φ (𝟙 (pathChainBimodule B a b R)) :=
  (rfl)

/-- **Along a Moore path, basepoint change preserves and reflects quasi-isomorphisms.** -/
theorem isQuasiIso_basepointChange_map_iff (hab : Nonempty (MoorePathBetween B a b))
    {M N : DGLocalSystem.{v} B a R} (φ : M ⟶ N) :
    DGRightModuleCat.IsQuasiIso ((basepointChange R a b).map φ) ↔
      DGRightModuleCat.IsQuasiIso φ :=
  isQuasiIso_tensorBimoduleMap_pathChainBimodule_iff hab

end DGLocalSystem

end TauCeti
