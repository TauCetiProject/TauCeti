/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Bimodule
public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Differential
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Grading.Basic
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Composition of path chains

Concatenation of Moore paths induces a bilinear composition of normalized cubical chains.
It is strictly associative after reindexing dimensions, satisfies the signed Leibniz rule,
and is balanced over the chains of loops at the intermediate basepoint. Consequently it
induces a specified map from the balanced tensor product of two path-chain modules to the
path-chain module between the outer endpoints.

This is the composition pairing used to compare successive changes of basepoint of DG
local systems. The tensor product here is ordinary; no derived equivalence is asserted.
The construction uses `NormalizedCubicalChain.map_crossProduct_map_assoc` for associativity
and `BalancedTensorProduct.lift` for descent through the balancing relations.

## References

* W. S. Massey, *Singular Homology Theory*, Chapter VII, for the cubical cross product.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public noncomputable section

open MulOpposite

namespace TauCeti

variable {B : Type*} [TopologicalSpace B] {a b c d : B}

namespace NormalizedCubicalChain

variable (R : Type*) [CommRing R]

/-- Compose path chains by taking their cross product and then concatenating paths. -/
def pathComp (a b c : B) (p q : ℕ) :
    NormalizedCubicalChain (MoorePathBetween B a b) R p →ₗ[R]
      NormalizedCubicalChain (MoorePathBetween B b c) R q →ₗ[R]
        NormalizedCubicalChain (MoorePathBetween B a c) R (p + q) :=
  (crossProduct _ _ R p q).compr₂ (map R (MoorePathBetween.transMap a b c) (p + q))

variable {R}

/-- Composition is the push-forward of the cubical cross product. -/
theorem pathComp_def {p q : ℕ} (x : NormalizedCubicalChain (MoorePathBetween B a b) R p)
    (y : NormalizedCubicalChain (MoorePathBetween B b c) R q) :
    pathComp R a b c p q x y = map R (MoorePathBetween.transMap a b c) (p + q)
      (crossProduct _ _ R p q x y) := (rfl)

/-- On cubes, composition concatenates the two paths with disjoint parameter blocks. -/
@[simp]
theorem pathComp_ofCube {p q : ℕ} (σ : SingularCube (MoorePathBetween B a b) p)
    (τ : SingularCube (MoorePathBetween B b c) q) :
    pathComp R a b c p q (ofCube _ R σ) (ofCube _ R τ) =
      ofCube _ R ((MoorePathBetween.transMap a b c).comp (SingularCube.crossProduct σ τ)) := by
  simp [pathComp_def]

/-- Path-chain composition is strictly associative after reindexing dimensions. -/
theorem pathComp_assoc {p q r : ℕ}
    (x : NormalizedCubicalChain (MoorePathBetween B a b) R p)
    (y : NormalizedCubicalChain (MoorePathBetween B b c) R q)
    (z : NormalizedCubicalChain (MoorePathBetween B c d) R r) :
    cast R (Nat.add_assoc p q r)
        (pathComp R a c d (p + q) r (pathComp R a b c p q x y) z) =
      pathComp R a b d p (q + r) x (pathComp R b c d q r y z) := by
  simp only [pathComp_def]
  refine map_crossProduct_map_assoc R ?_ x y z
  apply ContinuousMap.ext
  intro t
  simpa [Homeomorph.prodAssoc, Equiv.prodAssoc, Prod.map] using
    MoorePathBetween.trans_assoc t.1.1 t.1.2 t.2

/-- A loop chain at the intermediate endpoint can be moved between the two factors. -/
theorem pathComp_balance {p q r : ℕ}
    (x : NormalizedCubicalChain (MoorePathBetween B a b) R p)
    (ω : NormalizedCubicalChain (MooreLoopSpace B b) R q)
    (y : NormalizedCubicalChain (MoorePathBetween B b c) R r) :
    cast R (Nat.add_assoc p q r)
        (pathComp R a b c (p + q) r (act _ _ R p q x ω) y) =
      pathComp R a b c p (q + r) x (leftAct _ _ R q r ω y) := by
  simp only [pathComp_def, act_def, leftAct_def]
  refine map_crossProduct_map_assoc R ?_ x ω y
  apply ContinuousMap.ext
  intro t
  apply MoorePathBetween.ext
  simp [Homeomorph.prodAssoc, Equiv.prodAssoc, Prod.map, MoorePath.trans_assoc]

/-- The constant path of duration zero is a left unit for chain composition. -/
@[simp]
theorem pathComp_one_left {q : ℕ}
    (y : NormalizedCubicalChain (MoorePathBetween B a b) R q) :
    cast R (Nat.zero_add q) (pathComp R a a b 0 q
      (ofCube _ R (SingularCube.point (MoorePathBetween.loopHomeomorph a 1))) y) = y := by
  rw [pathComp_def, ← map_cast, crossProduct_point_left, ← LinearMap.comp_apply, ← map_comp]
  have h : (MoorePathBetween.transMap a a b).comp
      (ContinuousMap.prodMk (ContinuousMap.const _ (MoorePathBetween.loopHomeomorph a 1))
        (ContinuousMap.id _)) = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro γ
    apply MoorePathBetween.ext
    simp
  rw [h, map_id, LinearMap.id_apply]

/-- The constant path of duration zero is a right unit for chain composition. -/
@[simp]
theorem pathComp_one_right {p : ℕ}
    (x : NormalizedCubicalChain (MoorePathBetween B a b) R p) :
    pathComp R a b b p 0 x
      (ofCube _ R (SingularCube.point (MoorePathBetween.loopHomeomorph b 1))) = x := by
  have hcast : cast R (Nat.add_zero p) (pathComp R a b b p 0 x
      (ofCube _ R (SingularCube.point (MoorePathBetween.loopHomeomorph b 1)))) = x := by
    rw [pathComp_def, ← map_cast, crossProduct_point_right,
      ← LinearMap.comp_apply, ← map_comp]
    have h : (MoorePathBetween.transMap a b b).comp
        (ContinuousMap.prodMk (ContinuousMap.id _)
          (ContinuousMap.const _ (MoorePathBetween.loopHomeomorph b 1))) = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro γ
      apply MoorePathBetween.ext
      simp
    rw [h, map_id, LinearMap.id_apply]
  simpa only [Nat.add_zero, cast_rfl] using hcast

/-- Composition satisfies the signed Leibniz rule in positive dimensions. -/
theorem boundary_pathComp {p q : ℕ}
    (x : NormalizedCubicalChain (MoorePathBetween B a b) R (p + 1))
    (y : NormalizedCubicalChain (MoorePathBetween B b c) R (q + 1)) :
    boundary _ R (p + q + 1)
        (cast R (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1)
          (pathComp R a b c (p + 1) (q + 1) x y)) =
      pathComp R a b c p (q + 1) (boundary _ R p x) y +
        (-1 : R) ^ (p + 1) • cast R (by omega : (p + 1) + q = p + q + 1)
          (pathComp R a b c (p + 1) q x (boundary _ R q y)) := by
  simp only [pathComp_def]
  rw [← map_cast, ← LinearMap.comp_apply (boundary _ R _), ← map_boundary,
    LinearMap.comp_apply, boundary_crossProduct, map_add, map_smul, map_cast]
  rfl

/-- Leibniz when the second path chain has dimension zero. -/
theorem boundary_pathComp_zero_right {p : ℕ}
    (x : NormalizedCubicalChain (MoorePathBetween B a b) R (p + 1))
    (y : NormalizedCubicalChain (MoorePathBetween B b c) R 0) :
    boundary _ R p (pathComp R a b c (p + 1) 0 x y) =
      pathComp R a b c p 0 (boundary _ R p x) y := by
  simp only [pathComp_def]
  rw [← LinearMap.comp_apply (boundary _ R p), ← map_boundary, LinearMap.comp_apply,
    boundary_crossProduct_zero_right]
  rfl

/-- Leibniz when the first path chain has dimension zero. -/
theorem boundary_pathComp_zero_left {q : ℕ}
    (x : NormalizedCubicalChain (MoorePathBetween B a b) R 0)
    (y : NormalizedCubicalChain (MoorePathBetween B b c) R (q + 1)) :
    boundary _ R q (cast R (Nat.zero_add (q + 1)) (pathComp R a b c 0 (q + 1) x y)) =
      cast R (Nat.zero_add q) (pathComp R a b c 0 q x (boundary _ R q y)) := by
  simp only [pathComp_def]
  rw [← map_cast, ← LinearMap.comp_apply (boundary _ R q), ← map_boundary,
    LinearMap.comp_apply, boundary_crossProduct_zero_left, map_cast]

end NormalizedCubicalChain

open NormalizedCubicalChain

variable (R : Type*) [CommRing R]

/-- Composition on the total modules of path chains, adding cubical dimensions. -/
def pathChainComp (a b c : B) :
    cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R →ₗ[R]
      cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R →ₗ[R]
        cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R :=
  cubicalChainModuleDesc fun p ↦
    (cubicalChainModuleDesc fun q ↦
      ((pathComp R a b c p q).compr₂ (cubicalChainModuleLof _ _ R (p + q))).flip).flip

/-- Composition on homogeneous chains agrees with the dimensionwise composition. -/
@[simp]
theorem pathChainComp_lof_lof {p q : ℕ}
    (x : NormalizedCubicalChain (MoorePathBetween B a b) R p)
    (y : NormalizedCubicalChain (MoorePathBetween B b c) R q) :
    pathChainComp R a b c (cubicalChainModuleLof _ _ R p x) (cubicalChainModuleLof _ _ R q y) =
      cubicalChainModuleLof _ _ R (p + q) (pathComp R a b c p q x y) := by
  simp [pathChainComp]

/-- Composition of total path chains is strictly associative. -/
theorem pathChainComp_assoc
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (y : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R)
    (z : cubicalChainModule (MoorePathBetween B c d) (MooreLoopSpace B d) R) :
    pathChainComp R a c d (pathChainComp R a b c x y) z =
      pathChainComp R a b d x (pathChainComp R b c d y z) := by
  induction x using cubicalChainModule.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | lof p x =>
    induction y using cubicalChainModule.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | lof q y =>
      induction z using cubicalChainModule.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | lof r z =>
        rw [pathChainComp_lof_lof, pathChainComp_lof_lof,
          pathChainComp_lof_lof, pathChainComp_lof_lof,
          ← pathComp_assoc, cubicalChainModuleLof_cast]

/-- The zero-duration constant path acts as a left identity on total chains. -/
@[simp]
theorem pathChainComp_one_left
    (y : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    pathChainComp R a a b (cubicalChainModuleLof _ _ R 0
      (ofCube _ R (SingularCube.point (MoorePathBetween.loopHomeomorph a 1)))) y = y := by
  induction y using cubicalChainModule.induction_on with
  | zero => simp
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | lof q y =>
    rw [pathChainComp_lof_lof, ← cubicalChainModuleLof_cast (Nat.zero_add q), pathComp_one_left]

/-- The zero-duration constant path acts as a right identity on total chains. -/
@[simp]
theorem pathChainComp_one_right
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    pathChainComp R a b b x (cubicalChainModuleLof _ _ R 0
      (ofCube _ R (SingularCube.point (MoorePathBetween.loopHomeomorph b 1)))) = x := by
  induction x using cubicalChainModule.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | lof p x =>
    rw [pathChainComp_lof_lof, pathComp_one_right]
    simp only [Nat.add_zero]

/-- Composition adds cohomological degrees (cubical dimension is negated). -/
theorem pathChainComp_mem {i j : ℤ}
    {x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R}
    {y : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R}
    (hx : x ∈ cubicalChainModuleGrading _ _ R i)
    (hy : y ∈ cubicalChainModuleGrading _ _ R j) :
    pathChainComp R a b c x y ∈ cubicalChainModuleGrading _ _ R (i + j) := by
  rcases mem_cubicalChainModuleGrading_iff.mp hx with rfl | ⟨p, x, hp, rfl⟩
  · simp
  rcases mem_cubicalChainModuleGrading_iff.mp hy with rfl | ⟨q, y, hq, rfl⟩
  · simp
  rw [pathChainComp_lof_lof]
  exact mem_cubicalChainModuleGrading_iff.mpr (.inr ⟨p + q, _, by push_cast; omega, rfl⟩)

private theorem pathChainComp_differential_lof {p q : ℕ}
    (x : NormalizedCubicalChain (MoorePathBetween B a b) R p)
    (y : NormalizedCubicalChain (MoorePathBetween B b c) R q) :
    cubicalChainModuleDifferential _ _ R
        (pathChainComp R a b c (cubicalChainModuleLof _ _ R p x)
          (cubicalChainModuleLof _ _ R q y)) =
      pathChainComp R a b c
        (cubicalChainModuleDifferential _ _ R (cubicalChainModuleLof _ _ R p x))
        (cubicalChainModuleLof _ _ R q y) +
      (-1 : R) ^ p • pathChainComp R a b c (cubicalChainModuleLof _ _ R p x)
        (cubicalChainModuleDifferential _ _ R (cubicalChainModuleLof _ _ R q y)) := by
  rw [pathChainComp_lof_lof]
  rcases p with _ | p <;> rcases q with _ | q
  · simp [cubicalChainModuleDifferential_lof_zero]
  · rw [← cubicalChainModuleLof_cast (Nat.zero_add (q + 1)),
      cubicalChainModuleDifferential_lof_succ, boundary_pathComp_zero_left,
      cubicalChainModuleLof_cast, cubicalChainModuleDifferential_lof_zero,
      cubicalChainModuleDifferential_lof_succ, pathChainComp_lof_lof]
    simp
  · rw [cubicalChainModuleDifferential_lof_succ, boundary_pathComp_zero_right,
      cubicalChainModuleDifferential_lof_succ, cubicalChainModuleDifferential_lof_zero,
      pathChainComp_lof_lof]
    simp
  · rw [← cubicalChainModuleLof_cast (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1),
      cubicalChainModuleDifferential_lof_succ, boundary_pathComp,
      map_add, map_smul, cubicalChainModuleLof_cast,
      cubicalChainModuleDifferential_lof_succ, cubicalChainModuleDifferential_lof_succ,
      pathChainComp_lof_lof, pathChainComp_lof_lof]
    rfl

/-- The signed Leibniz rule for total composition. Only the first input must be homogeneous. -/
theorem pathChainComp_differential {i : ℤ}
    {x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R}
    (hx : x ∈ cubicalChainModuleGrading _ _ R i)
    (y : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    cubicalChainModuleDifferential _ _ R (pathChainComp R a b c x y) =
      pathChainComp R a b c (cubicalChainModuleDifferential _ _ R x) y +
        i.negOnePow • pathChainComp R a b c x (cubicalChainModuleDifferential _ _ R y) := by
  rcases mem_cubicalChainModuleGrading_iff.mp hx with rfl | ⟨p, x, hp, rfl⟩
  · simp
  obtain rfl : i = -(p : ℤ) := by omega
  rw [negOnePow_neg_natCast_smul_cubicalChainModule]
  induction y using cubicalChainModule.induction_on with
  | zero => simp
  | lof q y => exact pathChainComp_differential_lof R x y
  | add y y' hy hy' => simp only [map_add, hy, hy', smul_add]; abel

/-- The total composition pairing is balanced over the intermediate loop-chain algebra. -/
theorem pathChainComp_balance (ω : loopChainAlgebra B b R)
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (y : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainComp R a b c (op ω • x) y = pathChainComp R a b c x (ω • y) := by
  induction x using cubicalChainModule.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [smul_add, map_add, LinearMap.add_apply, hx, hx']
  | lof p x =>
    induction y using cubicalChainModule.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [smul_add, map_add, hy, hy']
    | lof r y =>
      induction ω using DirectSum.induction_on with
      | zero => simp
      | add ω ω' hω hω' => simp only [op_add, add_smul, map_add, LinearMap.add_apply, hω, hω']
      | of q ω =>
        rw [← DirectSum.lof_eq_of R, op_lof_smul_cubicalChainModuleLof,
          lof_smul_cubicalChainModuleLof, pathChainComp_lof_lof, pathChainComp_lof_lof,
          ← pathComp_balance, cubicalChainModuleLof_cast]

/-- Concatenation descends to the tensor product balanced over intermediate loop chains. -/
def pathChainTensorComp (a b c : B) :
    BalancedTensorProduct R (loopChainAlgebra B b R)
      (cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
      (cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) →ₗ[R]
        cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R :=
  BalancedTensorProduct.lift (pathChainComp R a b c) (pathChainComp_balance R)

/-- The balanced composition map concatenates the two factors of a pure tensor. -/
@[simp]
theorem pathChainTensorComp_tmul
    (x : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
    (y : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    pathChainTensorComp R a b c (BalancedTensorProduct.tmul R (loopChainAlgebra B b R) x y) =
      pathChainComp R a b c x y := by
  rw [pathChainTensorComp, BalancedTensorProduct.lift_tmul]

/-- The balanced composition map commutes with the balanced tensor differential. -/
theorem pathChainTensorComp_differential
    (z : BalancedTensorProduct R (loopChainAlgebra B b R)
      (cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
      (cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R)) :
    pathChainTensorComp R a b c
        (BalancedTensorProduct.differential
          (pathChain_isDGBimodule B a b R).isDGRightModule
          (pathChain_isDGBimodule B b c R).toIsDGLeftModule z) =
      cubicalChainModuleDifferential _ _ R (pathChainTensorComp R a b c z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => simp only [map_add, hz, hz']
  | ht x y =>
    induction x using cubicalChainModule.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [BalancedTensorProduct.add_tmul, map_add, hx, hx']
    | lof p x =>
      have hx : cubicalChainModuleLof _ _ R p x ∈
          cubicalChainModuleGrading (MoorePathBetween B a b) (MooreLoopSpace B b) R
            (-(p : ℤ)) := mem_cubicalChainModuleGrading_iff.mpr (.inr ⟨p, x, by omega, rfl⟩)
      rw [BalancedTensorProduct.differential_tmul_of_mem
          (pathChain_isDGBimodule B a b R).isDGRightModule
          (pathChain_isDGBimodule B b c R).toIsDGLeftModule hx,
        map_add, map_smul, pathChainTensorComp_tmul, pathChainTensorComp_tmul,
        pathChainTensorComp_tmul, pathChainComp_differential R hx]
      simp only [negOnePow_smul_eq_negOnePowCast_smul (R := R), negOnePowCast_eq_intCast]

section Grading

-- The packaged internal grading has the same pieces as the cubical module grading.
local instance : SetLike.GradedSMul
    (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B b) R)).opposite.piece
    (InternalGrading.ofDecomposition
      (cubicalChainModuleGrading (MoorePathBetween B a b) (MooreLoopSpace B b) R)).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

local instance : SetLike.GradedSMul (cubicalChainGrading (MooreLoopSpace B b) R)
    (InternalGrading.ofDecomposition
      (cubicalChainModuleGrading (MoorePathBetween B b c) (MooreLoopSpace B c) R)).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Balanced composition preserves the total cohomological grading. -/
theorem pathChainTensorComp_mem {i : ℤ}
    {z : BalancedTensorProduct R (loopChainAlgebra B b R)
      (cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R)
      (cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R)}
    (hz : z ∈ (BalancedTensorProduct.grading
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (InternalGrading.ofDecomposition (cubicalChainModuleGrading
        (MoorePathBetween B a b) (MooreLoopSpace B b) R))
      (InternalGrading.ofDecomposition (cubicalChainModuleGrading
        (MoorePathBetween B b c) (MooreLoopSpace B c) R))).piece i) :
    pathChainTensorComp R a b c z ∈ cubicalChainModuleGrading _ _ R i := by
  simpa only [add_zero] using BalancedTensorProduct.map_mem_of_tmul _ _
    (cubicalChainModuleGrading (MoorePathBetween B a c) (MooreLoopSpace B c) R)
    (pathChainTensorComp R a b c) 0 (fun hx hy ↦ by
      rw [InternalGrading.ofDecomposition_piece] at hx hy
      simpa only [pathChainTensorComp_tmul, add_zero] using pathChainComp_mem R hx hy) hz

end Grading

end TauCeti
