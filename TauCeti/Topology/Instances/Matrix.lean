/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Matrix
public import Mathlib.Topology.Metrizable.Basic
public import TauCeti.LinearAlgebra.Matrix.TensorProduct
public import TauCeti.Topology.Algebra.IsOpenUnits

/-!
# Topological properties of matrices

Mathlib gives `Matrix m n α` the product topology of `m → n → α`, so for finite index types it is
pseudo-metrizable whenever `α` is. This makes metrizable-codomain results, such as measurability
of pointwise limits of measurable maps, available for matrix-valued functions without choosing a
matrix norm.

Matrices with countably many rows and columns are second countable when their entries are, and
matrices with finitely many rows and columns are σ-compact when their entries are.

Square matrices act jointly continuously on column vectors by `Matrix.mulVec`, the action of
`Mathlib.LinearAlgebra.Matrix.Action`; through the unit group, so does `GL n R`
(`Units.continuousSMul`).

The same product topology gives entrywise control of a real matrix-valued map near a point of
continuity, again without a matrix norm
(`ContinuousAt.exists_ball_subset_forall_abs_sub_le`), and the product uniformity gives the
uniform version for uniformly continuous maps (`UniformContinuous.exists_pos_forall_abs_sub_le`).

Over a topological field, the inverse of a matrix-valued function that is continuous at a point
with invertible value is continuous there (`ContinuousAt.matrix_inv`), and so are its entries
(`ContinuousAt.matrix_inv_apply`).

Square matrices over a commutative topological ring `R` with open units again have open units
(`Matrix.instIsOpenUnits`). The invertible matrices are the preimage of the open set of units of
`R` under the continuous determinant, and the inverse `A⁻¹ = (det A)⁻¹ • adj A` is continuous on
them because the inverse of the determinant is. Over a nonarchimedean local field `E`, which has
open units because it is a Hausdorff topological field, this says that `GL_n(E)` with the
topology of the unit group is the open subspace `{det ≠ 0}` of the matrices `M_n(E)`. The
hypothesis on `R` cannot be dropped: over the adeles, inversion is not continuous on the units
for the subspace topology, already for `n = 1`.

Each characteristic coefficient is continuous over a commutative topological ring
(`Matrix.continuous_charpoly_coeff`). The proof uses Mathlib's universal characteristic polynomial
`Matrix.charpoly.univ`, whose coefficients are multivariate polynomials in the matrix entries.

The Kronecker product of two continuously varying matrices is continuous in the product topology.
In particular the ⋆-algebra homomorphisms `A ↦ A ⊗ₖ 1` and `B ↦ 1 ⊗ₖ B` are continuous.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  §3, pp. 3–4.
-/

public section

namespace TauCeti

/-- A space of matrices with finitely many rows and columns over a pseudo-metrizable space is
pseudo-metrizable. -/
instance {m n α : Type*} [Finite m] [Finite n] [TopologicalSpace α]
    [TopologicalSpace.PseudoMetrizableSpace α] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix m n α) :=
  -- The topology of `Matrix m n α` is by definition the product topology on `m → n → α`.
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (m → n → α))

/-- Matrices with countably many rows and columns over a second-countable space are
second countable. -/
instance {m n α : Type*} [Countable m] [Countable n] [TopologicalSpace α]
    [SecondCountableTopology α] : SecondCountableTopology (Matrix m n α) :=
  inferInstanceAs (SecondCountableTopology (m → n → α))

/-- Matrices with finitely many rows and columns over a σ-compact space form a σ-compact space. -/
instance {m n α : Type*} [Finite m] [Finite n] [TopologicalSpace α] [SigmaCompactSpace α] :
    SigmaCompactSpace (Matrix m n α) :=
  inferInstanceAs (SigmaCompactSpace (m → n → α))

/-- Square matrices act jointly continuously on column vectors by `Matrix.mulVec`. -/
instance {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R] [TopologicalSpace R]
    [ContinuousAdd R] [ContinuousMul R] : ContinuousSMul (Matrix n n R) (n → R) :=
  ⟨continuous_fst.matrix_mulVec continuous_snd⟩

end TauCeti

namespace ContinuousAt

open Filter Metric
open scoped Topology

/-- If a real matrix-valued map `a` on a pseudo-metric space is continuous at `x`, then for every
neighbourhood `s` of `x` and every `ε > 0` there is a ball `B(x, r) ⊆ s` on which every entry of
`a` differs from its value at `x` by at most `ε`. -/
theorem exists_ball_subset_forall_abs_sub_le {X m n : Type*} [PseudoMetricSpace X] [Finite m]
    [Finite n] {a : X → Matrix m n ℝ} {x : X} (hcont : ContinuousAt a x) {s : Set X}
    (hs : s ∈ 𝓝 x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ s ∧ ∀ y ∈ ball x r, ∀ i j, |a y i j - a x i j| ≤ ε := by
  have hev : ∀ᶠ y in 𝓝 x, y ∈ s ∧ ∀ i j, |a y i j - a x i j| ≤ ε := by
    refine Eventually.and hs (eventually_all.2 fun i => eventually_all.2 fun j => ?_)
    have hij : ContinuousAt (fun y => a y i j) x :=
      (continuous_id.matrix_elem i j).continuousAt.comp hcont
    filter_upwards [Metric.tendsto_nhds.1 hij ε hε] with y hy
    exact (Real.dist_eq _ _ ▸ hy).le
  obtain ⟨r, hr, hrx⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact ⟨r, hr, fun y hy => (hrx y hy).1, fun y hy => (hrx y hy).2⟩

end ContinuousAt

namespace UniformContinuous

open Filter Metric
open scoped Uniformity

/-- If a real matrix-valued map `a` on a pseudo-metric space is uniformly continuous, then for every
`ε > 0` there is `r > 0` such that every entry of `a` varies by at most `ε` between any two points
at distance less than `r`. -/
theorem exists_pos_forall_abs_sub_le {X m n : Type*} [PseudoMetricSpace X] [Finite m] [Finite n]
    {a : X → Matrix m n ℝ} (ha : UniformContinuous a) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x y, dist x y < r → ∀ i j, |a x i j - a y i j| ≤ ε := by
  have hev : ∀ᶠ z : X × X in 𝓤 X, ∀ i j, |a z.1 i j - a z.2 i j| ≤ ε := by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have hij : UniformContinuous fun x => a x i j := (Matrix.uniformContinuous _ _ _).1 ha i j
    filter_upwards [hij (dist_mem_uniformity hε)] with z hz
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Real.dist_eq] at hz
    exact hz.le
  obtain ⟨r, hr, hrz⟩ := uniformity_basis_dist.mem_iff.1 hev
  exact ⟨r, hr, fun x y hxy => @hrz (x, y) hxy⟩

end UniformContinuous

section Inverse

variable {X n K : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n] [Field K]
  [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] {A : X → Matrix n n K} {x : X}

/-- The inverse of a matrix-valued function is continuous at every point where the function is
continuous and its value is invertible. -/
theorem ContinuousAt.matrix_inv (hA : ContinuousAt A x) (hdet : (A x).det ≠ 0) :
    ContinuousAt (fun y ↦ (A y)⁻¹) x :=
  (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)).comp hA

/-- The entries of the inverse of a matrix-valued function are continuous at every point where the
function is continuous and its value is invertible. -/
theorem ContinuousAt.matrix_inv_apply (hA : ContinuousAt A x) (hdet : (A x).det ≠ 0) (k l : n) :
    ContinuousAt (fun y ↦ (A y)⁻¹ k l) x :=
  (continuous_apply_apply k l).continuousAt.comp (hA.matrix_inv hdet)

end Inverse

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R]

/-- Every characteristic coefficient is continuous for the entrywise matrix topology. -/
@[continuity, fun_prop]
theorem continuous_charpoly_coeff (k : ℕ) :
    Continuous (fun A : Matrix n n R => A.charpoly.coeff k) := by
  have h : Continuous (fun A : Matrix n n R =>
      MvPolynomial.eval (Function.uncurry A) ((charpoly.univ R n).coeff k)) :=
    (MvPolynomial.continuous_eval (p := (charpoly.univ R n).coeff k)).comp
      (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)
  have hmatrix (A : Matrix n n R) : of (Function.curry (Function.uncurry A)) = A := by
    ext i j
    rfl
  simpa only [MvPolynomial.eval, charpoly.univ_coeff_eval₂Hom, hmatrix] using h

variable [IsOpenUnits R]

/-- Square matrices over a commutative topological ring with open units have open units: the
invertible matrices form an open set on which inversion is continuous. -/
instance instIsOpenUnits : IsOpenUnits (Matrix n n R) where
  isOpenEmbedding_unitsVal := by
    refine ⟨Units.isEmbedding_val_mk' (f := Inv.inv) (fun A hA ↦ ?_)
      fun u ↦ (coe_units_inv u).symm, ?_⟩
    · obtain ⟨u, hu⟩ := (isUnit_iff_isUnit_det A).1 hA
      exact (continuousAt_matrix_inv A
        (hu ▸ IsOpenUnits.continuousAt_ringInverse u)).continuousWithinAt
    · have hrange : Set.range (Units.val : (Matrix n n R)ˣ → Matrix n n R) =
          det ⁻¹' Set.range (Units.val : Rˣ → R) := by
        ext A
        exact isUnit_iff_isUnit_det A
      rw [hrange]
      exact IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.preimage continuous_id.matrix_det

end Matrix

open scoped Kronecker

/-- The Kronecker product of two continuous matrix-valued functions is continuous. -/
@[continuity, fun_prop]
theorem Continuous.matrix_kronecker {X R l m n p : Type*} [TopologicalSpace X]
    [TopologicalSpace R] [Mul R] [ContinuousMul R]
    {A : X → Matrix l m R} {B : X → Matrix n p R}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x ↦ A x ⊗ₖ B x) := by
  apply continuous_matrix
  intro i j
  simp only [Matrix.kroneckerMap_apply]
  exact (hA.matrix_elem i.1 j.1).mul (hB.matrix_elem i.2 j.2)

namespace Matrix

variable {R m n : Type*} [CommSemiring R] [StarRing R] [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n] [TopologicalSpace R] [ContinuousMul R]

@[continuity, fun_prop]
theorem continuous_kroneckerOneStarAlgHom :
    Continuous (kroneckerOneStarAlgHom R (m := m) n) :=
  (continuous_id.matrix_kronecker continuous_const).congr fun A ↦
    (kroneckerOneStarAlgHom_apply A).symm

@[continuity, fun_prop]
theorem continuous_oneKroneckerStarAlgHom :
    Continuous (oneKroneckerStarAlgHom R (m := m) n) :=
  (continuous_const.matrix_kronecker continuous_id).congr fun B ↦
    (oneKroneckerStarAlgHom_apply B).symm

end Matrix
