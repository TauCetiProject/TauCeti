/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BasepointChange
public import TauCeti.Topology.PathSpace.Moore.Comparison.Homotopic

/-!
# Changing the basepoint of a classical local system is parallel transport

A classical local system `L` on a space `X` is a DG local system at every point `a`: its fiber
`L_a`, concentrated in degree zero, on which a chain of Moore loops at `a` acts through its
degree-zero part in the group ring of `π₁(X, a)` (`TauCeti.classicalDGLocalSystem`). Changing the
basepoint to `b` tensors this DG local system with the chain bimodule `C_*(P_{a→b} X)` of Moore
paths from `a` to `b`. This file shows that the result is the DG local system of `L` at `b`, the
fiber `L_b` with its own monodromy, up to a specified quasi-isomorphism.

The comparison is parallel transport. A `0`-chain of Moore paths from `a` to `b` transports
`L_a` to `L_b` along the homotopy class of each of its paths, and chains of positive dimension act
by zero (`TauCeti.pathChainTransport`). Boundaries of `1`-chains act by zero, since the two ends
of a path in the space of Moore paths are homotopic paths
(`TauCeti.pathChainTransport_cubicalChainModuleDifferential`), and transport is compatible with
the Moore loops acting by concatenation at either end, which act on the fibers by monodromy. So
`m ⊗ c ↦ c(m)` is a morphism of DG local systems at `b`,
`L_a ⊗_{C_*(Ω_a X)} C_*(P_{a→b} X) → L_b` (`TauCeti.tensorPathChainTransport`), which sends
`m ⊗ [δ]` to the transport of `m` along `δ`
(`TauCeti.tensorPathChainTransport_tmul_pathChainPoint`).

It is a quasi-isomorphism as soon as `a` and `b` are joined by a path, say by a Moore path `δ`
(`TauCeti.tensorPathChainTransport_isQuasiIso`). The tensor product is a homotopy retract of
`L_a`, through `m ⊗ c ↦ m · ρ_δ(c)` and `m ↦ m ⊗ [δ]` (the general change of basepoint,
`TauCeti.tensorPathChainPoint_tensorPathChainAct`), and under this retraction the comparison is
transport along `δ`, an isomorphism `L_a ≅ L_b`. For `b = a`, the comparison is the isomorphism
`L_a ⊗ C_*(P_{a→a} X) ≅ L_a` of the unit law of basepoint change
(`TauCeti.tensorPathChainTransport_eq_tensorPathChainAct_one`).

## Main definitions

* `TauCeti.pathChainTransport`: parallel transport along the chains of Moore paths from `a` to
  `b`, as a linear map from these chains to the linear maps `L_a → L_b`.
* `TauCeti.tensorPathChainTransport`: the morphism of DG local systems
  `L_a ⊗ C_*(P_{a→b} X) → L_b`, `m ⊗ c ↦ c(m)`.

## Main results

* `TauCeti.pathChainTransport_cubicalChainModuleDifferential`: transport vanishes on boundaries.
* `TauCeti.pathChainTransport_smul`, `TauCeti.pathChainTransport_op_smul`: transport is
  compatible with the actions of the Moore loops at both ends, reduced to point chains by
  `TauCeti.pathChainTransport_pathChainPoint_leftAct` and
  `TauCeti.pathChainTransport_pathChainPoint_rightAct`.
* `TauCeti.tensorPathChainTransport_isQuasiIso`: within a path component, changing the basepoint
  of a classical local system is transport, up to quasi-isomorphism.
* `TauCeti.transport_comp_tensorPathChainAct`: under the retraction of the change of basepoint
  along a Moore path `δ`, the comparison is transport along `δ`.
* `TauCeti.tensorPathChainTransport_eq_tensorPathChainAct_one`: for `b = a`, the comparison is the
  unit isomorphism of basepoint change.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §§2.2 and 7.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.3.
-/

public noncomputable section

namespace TauCeti

open MulOpposite NormalizedCubicalChain

universe u w

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {a b : X}
  (L : LocalCoefficientSystem.{u, u, w} R X)

section Transport

/-- The degree-zero part of `pathChainTransport`: a formal combination of Moore paths from `a` to
`b` transports `L_a` to `L_b` along the homotopy classes of its paths. -/
private def pathChainTransportZero :
    NormalizedCubicalChain (MoorePathBetween X a b) R 0 →ₗ[R]
      L.obj (FundamentalGroupoid.mk a) →ₗ[R] L.obj (FundamentalGroupoid.mk b) :=
  Finsupp.linearCombination R (fun γ : MoorePathBetween X a b ↦
      (LocalCoefficientSystem.transport L (Path.Homotopic.Quotient.mk γ.toPath)).toLinearMap) ∘ₗ
    (zeroEquiv (MoorePathBetween X a b) R).toLinearMap

/-- The components of `pathChainTransport`: transport on `0`-chains, zero in positive
dimensions. -/
private def pathChainTransportComponent : ∀ n : ℕ,
    NormalizedCubicalChain (MoorePathBetween X a b) R n →ₗ[R]
      L.obj (FundamentalGroupoid.mk a) →ₗ[R] L.obj (FundamentalGroupoid.mk b)
  | 0 => pathChainTransportZero L
  | _ + 1 => 0

/-- **Parallel transport along chains of Moore paths**: a `0`-chain of Moore paths from `a` to
`b` transports the fiber `L_a` to `L_b` along the homotopy classes of its paths, and chains of
positive dimension act by zero. -/
def pathChainTransport :
    cubicalChainModule (MoorePathBetween X a b) (MooreLoopSpace X b) R →ₗ[R]
      L.obj (FundamentalGroupoid.mk a) →ₗ[R] L.obj (FundamentalGroupoid.mk b) :=
  cubicalChainModuleDesc (pathChainTransportComponent L)

/-- The `0`-chain of a `0`-cube of Moore paths transports along the homotopy class of its path. -/
theorem pathChainTransport_lof_zero_ofCube (c : SingularCube (MoorePathBetween X a b) 0) :
    pathChainTransport L (cubicalChainModuleLof _ _ R 0 (ofCube _ R c)) =
      (LocalCoefficientSystem.transport L
        (Path.Homotopic.Quotient.mk (c fun i ↦ i.elim0).toPath)).toLinearMap := by
  rw [SingularCube.eq_point c]
  simp [pathChainTransport, pathChainTransportComponent, pathChainTransportZero]

/-- **The `0`-chain of a Moore path transports along its homotopy class.** -/
@[simp]
theorem pathChainTransport_pathChainPoint (γ : MoorePathBetween X a b) :
    pathChainTransport L (pathChainPoint R γ) =
      (LocalCoefficientSystem.transport L (Path.Homotopic.Quotient.mk γ.toPath)).toLinearMap := by
  rw [pathChainPoint_def, pathChainTransport_lof_zero_ofCube, SingularCube.point_apply]

/-- Chains of positive dimension transport by zero. -/
@[simp]
theorem pathChainTransport_lof_succ (k : ℕ)
    (c : NormalizedCubicalChain (MoorePathBetween X a b) R (k + 1)) :
    pathChainTransport L (cubicalChainModuleLof _ (MooreLoopSpace X b) R (k + 1) c) = 0 := by
  simp [pathChainTransport, pathChainTransportComponent]

/-- Transport vanishes outside degree zero. -/
theorem pathChainTransport_eq_zero_of_mem {i : ℤ} (hi : i ≠ 0)
    {x : cubicalChainModule (MoorePathBetween X a b) (MooreLoopSpace X b) R}
    (hx : x ∈ cubicalChainModuleGrading _ _ R i) : pathChainTransport L x = 0 := by
  rcases mem_cubicalChainModuleGrading_iff.1 hx with rfl | ⟨n, c, hn, rfl⟩
  · exact map_zero _
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    exact pathChainTransport_lof_succ L k c

/-- The two ends of a `1`-cube of Moore paths have the same transport, since they are joined by
a path in the space of Moore paths. -/
private theorem pathChainTransportZero_boundary_ofCube
    (c : SingularCube (MoorePathBetween X a b) 1) :
    pathChainTransportZero L (boundary _ R 0 (ofCube _ R c)) = 0 := by
  have hjoined : Joined (c fun _ ↦ 0) (c fun _ ↦ 1) :=
    ⟨{ toFun := fun t ↦ c fun _ ↦ t
       continuous_toFun := by fun_prop
       source' := rfl
       target' := rfl }⟩
  have h : Path.Homotopic.Quotient.mk (c fun _ ↦ 0).toPath =
      Path.Homotopic.Quotient.mk (c fun _ ↦ 1).toPath :=
    Quotient.sound (MoorePathBetween.homotopic_toPath_of_joined hjoined)
  simp [pathChainTransportZero, SingularCube.face_eq_point, h]

/-- **Transport vanishes on boundaries**: the two ends of a path in the space of Moore paths from
`a` to `b` are homotopic paths, so they transport alike. -/
@[simp]
theorem pathChainTransport_cubicalChainModuleDifferential
    (x : cubicalChainModule (MoorePathBetween X a b) (MooreLoopSpace X b) R) :
    pathChainTransport L (cubicalChainModuleDifferential _ _ R x) = 0 := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', add_zero]
  | lof n c =>
    rcases n with _ | k
    · rw [cubicalChainModuleDifferential_lof_zero, map_zero]
    · rw [cubicalChainModuleDifferential_lof_succ]
      rcases k with _ | j
      · induction c using NormalizedCubicalChain.induction_on with
        | zero => simp
        | add c c' hc hc' => simp only [map_add, hc, hc', add_zero]
        | smul r c hc => simp only [map_smul, hc, smul_zero]
        | ofCube c =>
          simpa [pathChainTransport, pathChainTransportComponent] using
            pathChainTransportZero_boundary_ofCube L c
      · exact pathChainTransport_lof_succ L j _

/-- The `0`-chain of a Moore loop `ω` at `a` followed by a Moore path `γ` transports along `γ`
after transport along `ω`. -/
theorem pathChainTransport_pathChainPoint_leftAct (ω : MooreLoopSpace X a)
    (γ : MoorePathBetween X a b) :
    pathChainTransport L (pathChainPoint R (MoorePathBetween.leftAct ω γ)) =
      pathChainTransport L (pathChainPoint R γ) ∘ₗ
        (LocalCoefficientSystem.transport L (Path.Homotopic.Quotient.mk ω.toPath)).toLinearMap := by
  rw [pathChainTransport_pathChainPoint, pathChainTransport_pathChainPoint,
    Path.Homotopic.Quotient.eq.2 (MoorePathBetween.homotopic_toPath_leftAct ω γ),
    Path.Homotopic.Quotient.mk_trans, LocalCoefficientSystem.transport_trans,
    LinearEquiv.coe_trans]

/-- The `0`-chain of a Moore path `γ` followed by a Moore loop `ω` at `b` transports along `ω`
after transport along `γ`. -/
theorem pathChainTransport_pathChainPoint_rightAct (γ : MoorePathBetween X a b)
    (ω : MooreLoopSpace X b) :
    pathChainTransport L (pathChainPoint R (MoorePathBetween.rightAct γ ω)) =
      (LocalCoefficientSystem.transport L (Path.Homotopic.Quotient.mk ω.toPath)).toLinearMap ∘ₗ
        pathChainTransport L (pathChainPoint R γ) := by
  rw [pathChainTransport_pathChainPoint, pathChainTransport_pathChainPoint,
    Path.Homotopic.Quotient.eq.2 (MoorePathBetween.homotopic_toPath_rightAct γ ω),
    Path.Homotopic.Quotient.mk_trans, LocalCoefficientSystem.transport_trans,
    LinearEquiv.coe_trans]

/-- **Transport is compatible with the loops at `a`**: a chain of Moore loops at `a` acting in
front of a chain of paths acts, after transport, on the fiber `L_a` before it, by monodromy. -/
theorem pathChainTransport_smul (α : loopChainAlgebra X a R)
    (x : cubicalChainModule (MoorePathBetween X a b) (MooreLoopSpace X b) R) :
    pathChainTransport L (α • x) = pathChainTransport L x ∘ₗ classicalAction L (op α) := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, LinearMap.add_comp]
  | lof q c =>
    induction α using DirectSum.induction_on with
    | zero => simp
    | add α α' hα hα' => rw [add_smul, map_add, hα, hα', op_add, map_add, LinearMap.comp_add]
    | of p y =>
      rw [← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof]
      rcases p with _ | p
      · rcases q with _ | q
        · induction y using NormalizedCubicalChain.induction_on with
          | zero => simp
          | add y y' hy hy' =>
            simp only [map_add, LinearMap.add_apply, op_add, LinearMap.comp_add, hy, hy']
          | smul r y hy =>
            simp only [map_smul, LinearMap.smul_apply, op_smul, LinearMap.comp_smul, hy]
          | ofCube ω =>
            induction c using NormalizedCubicalChain.induction_on with
            | zero => simp
            | add c c' hc hc' =>
              simp only [map_add, LinearMap.add_comp, hc, hc']
            | smul r c hc =>
              simp only [map_smul, LinearMap.smul_comp, hc]
            | ofCube σ =>
              rw [SingularCube.eq_point ω, SingularCube.eq_point σ, leftAct_ofCube_point,
                classicalAction_lof_point, MoorePathBetween.smul_eq_leftAct,
                ← pathChainPoint_def, ← pathChainPoint_def,
                pathChainTransport_pathChainPoint_leftAct]
        · rw [pathChainTransport_eq_zero_of_mem L (by omega) (cubicalChainModuleLof_mem _),
            pathChainTransport_lof_succ, LinearMap.zero_comp]
      · rw [pathChainTransport_eq_zero_of_mem L (by omega) (cubicalChainModuleLof_mem _),
          classicalAction_lof_succ, LinearMap.comp_zero]

/-- **Transport is compatible with the loops at `b`**: a chain of Moore loops at `b` acting behind
a chain of paths acts, after transport, on the fiber `L_b` after it, by monodromy. -/
theorem pathChainTransport_op_smul (β : loopChainAlgebra X b R)
    (x : cubicalChainModule (MoorePathBetween X a b) (MooreLoopSpace X b) R) :
    pathChainTransport L (op β • x) = classicalAction L (op β) ∘ₗ pathChainTransport L x := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, LinearMap.comp_add]
  | lof p c =>
    induction β using DirectSum.induction_on with
    | zero => simp
    | add β β' hβ hβ' =>
      rw [MulOpposite.op_add, add_smul, map_add, hβ, hβ', map_add, LinearMap.add_comp]
    | of q y =>
      rw [← DirectSum.lof_eq_of R, op_lof_smul_cubicalChainModuleLof]
      rcases q with _ | q
      · rcases p with _ | p
        · induction y using NormalizedCubicalChain.induction_on with
          | zero => simp
          | add y y' hy hy' =>
            simp only [map_add, MulOpposite.op_add, LinearMap.add_comp, hy, hy']
          | smul r y hy =>
            simp only [map_smul, MulOpposite.op_smul, LinearMap.smul_comp, hy]
          | ofCube ω =>
            induction c using NormalizedCubicalChain.induction_on with
            | zero => simp
            | add c c' hc hc' =>
              simp only [map_add, LinearMap.add_apply, LinearMap.comp_add, hc, hc']
            | smul r c hc =>
              simp only [map_smul, LinearMap.smul_apply, LinearMap.comp_smul, hc]
            | ofCube σ =>
              rw [SingularCube.eq_point ω, SingularCube.eq_point σ, act_ofCube_point,
                classicalAction_lof_point, MoorePathBetween.op_smul_eq_rightAct,
                ← pathChainPoint_def, ← pathChainPoint_def,
                pathChainTransport_pathChainPoint_rightAct]
        · rw [pathChainTransport_eq_zero_of_mem L (by omega) (cubicalChainModuleLof_mem _),
            pathChainTransport_lof_succ, LinearMap.comp_zero]
      · rw [pathChainTransport_eq_zero_of_mem L (by omega) (cubicalChainModuleLof_mem _),
          classicalAction_lof_succ, LinearMap.zero_comp]

end Transport

section Tensor

open BalancedTensorProduct DGRightModuleCat

/-- The right action of the loop chains at `b` on `L_a ⊗ C_*(P_{a→b} X)`, which instance search
does not see through the carrier of the tensor product. -/
local instance :
    Module (loopChainAlgebra X b R)ᵐᵒᵖ
      (tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a b R)) :=
  (tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a b R)).moduleOp

/-- The ground ring and the loop chains at `b` act compatibly on `L_a ⊗ C_*(P_{a→b} X)`. -/
local instance :
    IsScalarTower R (loopChainAlgebra X b R)ᵐᵒᵖ
      (tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a b R)) :=
  (tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a b R)).scalarTower

/-- The loop chains at `b` act on `L_a ⊗ C_*(P_{a→b} X)` compatibly with the gradings. -/
local instance :
    SetLike.GradedSMul
      (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace X b) R)).opposite.piece
      (tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a b R)).grading :=
  (tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a b R)).gradedSMul

-- Transport the graded actions to the internal gradings used by balanced tensors.
local instance :
    SetLike.GradedSMul
      (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace X a) R)).opposite.piece
      (InternalGrading.ofDecomposition (classicalDGLocalSystem a L).grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  exact (classicalDGLocalSystem a L).gradedSMul

local instance : SetLike.GradedSMul (cubicalChainGrading (MooreLoopSpace X a) R)
    (InternalGrading.ofDecomposition (pathChainBimodule X a b R).grading).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- `m ⊗ c ↦ c(m)` on `L_a ⊗ C_*(P_{a→b} X)`, transporting `m` along the chain of paths `c`. -/
private def tensorPathChainTransportLinearMap :
    tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a b R) →ₗ[R]
      L.obj (FundamentalGroupoid.mk b) :=
  lift (pathChainTransport L).flip fun α m c ↦ by
    -- The factor `L_a` is the carrier of the classical DG local system, on which `op α` acts by
    -- `classicalAction L (op α)` by definition (`op_smul_eq_classicalAction`); `rw` cannot see
    -- through that carrier, so the goal is restated on the fiber of `L`.
    change pathChainTransport L c (classicalAction L (op α) m) = pathChainTransport L (α • c) m
    exact (LinearMap.congr_fun (pathChainTransport_smul L α c) m).symm

private theorem tensorPathChainTransportLinearMap_tmul (m : classicalDGLocalSystem a L)
    (c : cubicalChainModule (MoorePathBetween X a b) (MooreLoopSpace X b) R) :
    tensorPathChainTransportLinearMap L (tmul R (loopChainAlgebra X a R) m c) =
      pathChainTransport L c m :=
  lift_tmul _ _ m c

/-- The comparison vanishes on the image of the differential: every element of `L_a` lies in
degree zero with zero differential, and transport vanishes on boundaries of chains of paths. -/
private theorem tensorPathChainTransportLinearMap_differential
    (z : tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a b R)) :
    tensorPathChainTransportLinearMap L
      ((tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a b R)).differential
        z) = 0 := by
  refine BalancedTensorProduct.induction_on R (loopChainAlgebra X a R) z
    (fun (m : classicalDGLocalSystem a L) c ↦ ?_)
    (fun z z' hz hz' ↦ by rw [map_add, map_add, hz, hz', add_zero])
  rw [tensorBimoduleObj_differential_tmul (M := classicalDGLocalSystem a L) (p := 0) (m := m)
    (by rw [classicalDGLocalSystem_grading, trivialGrading_zero]; trivial),
    map_add, Units.smul_def, map_zsmul, tensorPathChainTransportLinearMap_tmul,
    tensorPathChainTransportLinearMap_tmul, pathChainTransport_cubicalChainModuleDifferential]
  -- The differential of the classical DG local system is zero
  -- (`classicalDGLocalSystem_differential`); restate the goal on the fiber of `L`, which `rw`
  -- does not see through the carrier of the DG local system.
  change pathChainTransport L c (0 : L.obj (FundamentalGroupoid.mk a)) +
      _ • (0 : L.obj (FundamentalGroupoid.mk a) →ₗ[R] L.obj (FundamentalGroupoid.mk b))
        (m : L.obj (FundamentalGroupoid.mk a)) = 0
  rw [map_zero, zero_add]
  exact smul_zero _

/-- **Changing the basepoint of a classical local system is parallel transport**: the morphism of
DG local systems at `b`, `L_a ⊗ C_*(P_{a→b} X) → L_b`, `m ⊗ c ↦ c(m)`, transporting `m` along the
chain of paths `c`. -/
def tensorPathChainTransport :
    DGRightModuleHom
      (tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a b R)).isDGRightModule
      (isDGRightModule_fiber (x := b) L) where
  toLinearMap :=
    { toFun := tensorPathChainTransportLinearMap L
      map_add' := map_add _
      map_smul' := fun β z ↦ by
        rw [← op_unop β, RingHom.id_apply]
        refine BalancedTensorProduct.induction_on R (loopChainAlgebra X a R) z
          (fun (m : classicalDGLocalSystem a L) c ↦ ?_)
          (fun z z' hz hz' ↦ by rw [smul_add, map_add, hz, hz', map_add, smul_add])
        rw [smul_tmul_right, tensorPathChainTransportLinearMap_tmul,
          tensorPathChainTransportLinearMap_tmul, pathChainTransport_op_smul]
        -- `op β` acts on `L_b` by `classicalAction L (op β)` (`op_smul_eq_classicalAction`).
        rfl }
  map_mem' := fun {q z} hz ↦ by
    have h := map_mem_of_tmul (𝒜 := cubicalChainGrading (MooreLoopSpace X a) R)
      (InternalGrading.ofDecomposition (classicalDGLocalSystem a L).grading)
      (InternalGrading.ofDecomposition (pathChainBimodule X a b R).grading)
      (trivialGrading R (L.obj (FundamentalGroupoid.mk b)))
      (tensorPathChainTransportLinearMap L) 0 (fun {p q} {m : classicalDGLocalSystem a L} {c}
          hm hc ↦ by
        rw [InternalGrading.ofDecomposition_piece, classicalDGLocalSystem_grading] at hm
        rw [InternalGrading.ofDecomposition_piece] at hc
        rw [tensorPathChainTransportLinearMap_tmul, mem_trivialGrading_iff]
        rcases (mem_trivialGrading_iff R (L.obj (FundamentalGroupoid.mk a))).1 hm with rfl | rfl
        · by_cases hq : q = 0
          · exact Or.inl (by omega)
          · exact Or.inr (by
              rw [pathChainTransport_eq_zero_of_mem L hq hc]
              -- `m` is an element of the carrier of `L_a`, the fiber of `L`.
              exact LinearMap.zero_apply (m : L.obj (FundamentalGroupoid.mk a)))
        · exact Or.inr (map_zero _)) hz
    rw [add_zero] at h
    exact h
  map_d' := fun z ↦ (tensorPathChainTransportLinearMap_differential L z).symm

@[simp]
theorem tensorPathChainTransport_tmul (m : classicalDGLocalSystem a L)
    (c : cubicalChainModule (MoorePathBetween X a b) (MooreLoopSpace X b) R) :
    tensorPathChainTransport L (tmul R (loopChainAlgebra X a R) m c) = pathChainTransport L c m :=
  tensorPathChainTransportLinearMap_tmul L m c

/-- `m ⊗ [δ]` goes to the transport of `m` along `δ`. -/
theorem tensorPathChainTransport_tmul_pathChainPoint (δ : MoorePathBetween X a b)
    (m : classicalDGLocalSystem a L) :
    tensorPathChainTransport L (tmul R (loopChainAlgebra X a R) m (pathChainPoint R δ)) =
      LocalCoefficientSystem.transport L (Path.Homotopic.Quotient.mk δ.toPath) m := by
  rw [tensorPathChainTransport_tmul, pathChainTransport_pathChainPoint, LinearEquiv.coe_coe]

/-- On the fiber `L_a`, the loop `ρ_δ(c)` acts by transport along `c` followed by transport back
along `δ`: transport along `δ` after the action of `ρ_δ(c)` is transport along `c`. -/
private theorem transport_comp_classicalAction_pathChainToLoopChain (δ : MoorePathBetween X a b)
    (c : cubicalChainModule (MoorePathBetween X a b) (MooreLoopSpace X b) R) :
    (LocalCoefficientSystem.transport L (Path.Homotopic.Quotient.mk δ.toPath)).toLinearMap ∘ₗ
        classicalAction L (op (pathChainToLoopChain R δ c)) =
      pathChainTransport L c := by
  induction c using cubicalChainModule.induction_on with
  | add c c' hc hc' =>
    rw [map_add, MulOpposite.op_add, map_add, LinearMap.comp_add, hc, hc', map_add]
  | lof n c =>
    rw [pathChainToLoopChain_lof]
    rcases n with _ | k
    · induction c using NormalizedCubicalChain.induction_on with
      | zero => simp
      | add c c' hc hc' =>
        rw [map_add, map_add, MulOpposite.op_add, map_add, LinearMap.comp_add, hc, hc', map_add,
          map_add]
      | smul r c hc =>
        rw [map_smul, map_smul, MulOpposite.op_smul, map_smul, LinearMap.comp_smul, hc, map_smul,
          map_smul]
      | ofCube σ =>
        -- The loop `ρ_δ(σ)` is `σ ⋆ δ⁻¹`, so its class followed by that of `δ` is that of `σ`.
        have hσ : MoorePathBetween.loopHomeomorph a
            ((MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun
              (σ fun i ↦ i.elim0)) = (σ fun i ↦ i.elim0).trans δ.symm :=
          MoorePathBetween.ext
            (by simp [MoorePathBetween.toMoorePath_loopAppendHomotopyEquiv_symm])
        have hpath := MoorePathBetween.homotopic_toPath_trans (σ fun i ↦ i.elim0) δ.symm
        rw [← hσ, MoorePathBetween.toPath_loopHomeomorph] at hpath
        have hclass : (Path.Homotopic.Quotient.mk
              ((MoorePathBetween.loopAppendHomotopyEquiv δ).symm.toFun
                (σ fun i ↦ i.elim0)).toPath).trans (Path.Homotopic.Quotient.mk δ.toPath) =
            Path.Homotopic.Quotient.mk (σ fun i ↦ i.elim0).toPath := by
          rw [Path.Homotopic.Quotient.eq.2 hpath]
          simp [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
            Path.Homotopic.Quotient.trans_assoc]
        rw [SingularCube.eq_point σ, map_ofCube, SingularCube.comp_point,
          classicalAction_lof_point, pathChainTransport_lof_zero_ofCube, SingularCube.point_apply,
          ← LinearEquiv.coe_trans, ← LocalCoefficientSystem.transport_trans, hclass]
    · rw [classicalAction_lof_succ, pathChainTransport_lof_succ, LinearMap.comp_zero]

/-- **The comparison is transport along a path, after the retraction of the change of
basepoint**: for a Moore path `δ` from `a` to `b`, following `m ⊗ c ↦ m · ρ_δ(c)` into `L_a` by
transport along `δ` is `m ⊗ c ↦ c(m)`. On a path `σ`, the loop `ρ_δ(σ) = σ ⋆ δ⁻¹` acts by
transport along it, and transport along `δ` then gives transport along `σ`. -/
theorem transport_comp_tensorPathChainAct (δ : MoorePathBetween X a b) :
    (LocalCoefficientSystem.transport L (Path.Homotopic.Quotient.mk δ.toPath)).toLinearMap ∘ₗ
        tensorPathChainAct (classicalDGLocalSystem a L) δ =
      (tensorPathChainTransport L).toLinearMap.restrictScalars R := by
  refine BalancedTensorProduct.hom_ext fun (m : classicalDGLocalSystem a L) c ↦ ?_
  -- Unfold the composite and the restriction of scalars on the pure tensor. The composite
  -- passes through the carrier of `classicalDGLocalSystem a L`, which is the fiber `L_a` only
  -- after unfolding a semireducible definition, so the goal is not type-correct at the
  -- transparency `rw` uses and `LinearMap.comp_apply` cannot fire.
  change LocalCoefficientSystem.transport L _
      (tensorPathChainAct (classicalDGLocalSystem a L) δ (tmul R (loopChainAlgebra X a R) m c)) =
    tensorPathChainTransport L (tmul R (loopChainAlgebra X a R) m c)
  rw [tensorPathChainTransport_tmul]
  refine (congrArg (LocalCoefficientSystem.transport L _)
    (tensorPathChainAct_tmul (classicalDGLocalSystem a L) δ m c)).trans ?_
  exact LinearMap.congr_fun (transport_comp_classicalAction_pathChainToLoopChain L δ c) m

/-- **For `b = a` the comparison is the unit isomorphism of basepoint change**: on
`L_a ⊗ C_*(P_{a→a} X)` it is `m ⊗ c ↦ m · ρ(c)`, reading chains of paths from `a` to itself as
chains of loops, the underlying map of the isomorphism `TauCeti.tensorPathChainOneIso`. -/
theorem tensorPathChainTransport_eq_tensorPathChainAct_one
    (z : tensorBimoduleObj (classicalDGLocalSystem a L) (pathChainBimodule X a a R)) :
    tensorPathChainTransport L z =
      tensorPathChainAct (classicalDGLocalSystem a L) (MoorePathBetween.loopHomeomorph a 1) z := by
  have h := LinearMap.congr_fun
    (transport_comp_tensorPathChainAct L (MoorePathBetween.loopHomeomorph a 1)) z
  rw [MoorePathBetween.toPath_loopHomeomorph, MooreLoopSpace.toPath_one,
    Path.Homotopic.Quotient.mk_refl,
    LocalCoefficientSystem.transport_refl] at h
  exact h.symm

/-- **Within a path component, changing the basepoint of a classical local system is transport,
up to quasi-isomorphism**: if a path joins `a` to `b`, the comparison
`L_a ⊗ C_*(P_{a→b} X) → L_b`, `m ⊗ c ↦ c(m)`, is a quasi-isomorphism of DG local systems at `b`.
The tensor product is a homotopy retract of `L_a`, and under the retraction the comparison is
transport along the path, an isomorphism. -/
theorem tensorPathChainTransport_isQuasiIso (h : Joined a b) :
    (tensorPathChainTransport (a := a) (b := b) L).IsQuasiIso := by
  obtain ⟨δ⟩ := nonempty_moorePathBetween_iff.2 h
  let M := classicalDGLocalSystem a L
  let e := LocalCoefficientSystem.transport L (Path.Homotopic.Quotient.mk δ.toPath)
  refine DGRightModuleHom.isQuasiIso_of_homotopyRetract (tensorPathChainTransport L)
    (dM₀ := M.differential) (dN₀ := (0 : L.obj (FundamentalGroupoid.mk b) →ₗ[R] _))
    e.toLinearMap ?_ (tensorPathChainAct M δ) (tensorPathChainPoint M δ)
    (tensorPathChainHomotopy M δ) LinearMap.id LinearMap.id 0
    (differential_tensorPathChainAct δ) (differential_tensorPathChainPoint δ)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (tensorPathChainPoint_tensorPathChainAct δ) (fun _ ↦ by simp)
    (fun z ↦ (LinearMap.congr_fun (transport_comp_tensorPathChainAct L δ) z).symm)
    (fun m ↦ ?_)
  · -- With zero differentials, the condition is that transport along `δ` is bijective.
    intro x y _ hxy
    have hx : e x = e 0 := by
      rw [map_zero]
      exact hxy
    refine ⟨e.symm y, 0, ?_, ?_⟩
    · -- The differential of `L_a` is zero.
      rw [e.injective hx, classicalDGLocalSystem_differential]
      -- `e.symm y` is an element of the fiber `L_a`, the carrier of the DG local system.
      exact LinearMap.zero_apply (e.symm y)
    · rw [LinearMap.zero_apply, add_zero]
      -- `e` is coerced to a linear map out of the carrier of `M`, which is the fiber `L_a` only
      -- up to unfolding, so `rw [LinearEquiv.coe_coe]` finds no instance of its pattern.
      exact (congrFun (LinearEquiv.coe_coe e) (e.symm y)).trans (e.apply_symm_apply y)
  · rw [tensorPathChainPoint_apply, tensorPathChainTransport_tmul_pathChainPoint,
      LinearMap.id_apply]
    -- `m` is an element of the carrier of `L_a`, the fiber of `L`, on which `e` acts.
    exact (congrFun (LinearEquiv.coe_coe e) (m : L.obj (FundamentalGroupoid.mk a))).symm

end Tensor

end TauCeti
