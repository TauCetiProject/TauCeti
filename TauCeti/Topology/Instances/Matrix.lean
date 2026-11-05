/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic
public import TauCeti.LinearAlgebra.Matrix.TensorProduct
public import TauCeti.Topology.Algebra.IsOpenUnits
public import TauCeti.Topology.MetricSpace.Holder

/-!
# Topological properties of matrices

Mathlib gives `Matrix m n α` the product topology of `m → n → α`, so for finite index types it is
pseudo-metrizable whenever `α` is. This makes metrizable-codomain results, such as measurability
of pointwise limits of measurable maps, available for matrix-valued functions without choosing a
matrix norm.

Matrices with countably many rows and columns are second countable when their entries are.

Square matrices act jointly continuously on column vectors by `Matrix.mulVec`, the action of
`Mathlib.LinearAlgebra.Matrix.Action`; through the unit group, so does `GL n R`
(`Units.continuousSMul`).

The same product topology gives entrywise control of a real matrix-valued map near a point of
continuity, again without a matrix norm
(`ContinuousAt.exists_ball_subset_forall_abs_sub_le`).

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

The Kronecker product of two continuously varying matrices is continuous in the product topology.
In particular the ⋆-algebra homomorphisms `A ↦ A ⊗ₖ 1` and `B ↦ 1 ⊗ₖ B` are continuous.

The entrywise inverse modulus and Hölder estimates are adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Matrix).

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
  [IsTopologicalRing R] [IsOpenUnits R]

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

section InverseHolder

open Set
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace X]

/--
**Entrywise modulus of the inverse.** For invertible `A`, `B` whose inverse entries are bounded by
`L ≥ 0` and whose
entrywise difference is bounded by `d ≥ 0`, `|A⁻¹ᵢⱼ − B⁻¹ᵢⱼ| ≤ n² L² d` with `n = card ι`, from
`A⁻¹ − B⁻¹ = A⁻¹ (B − A) B⁻¹`. -/
theorem Matrix.abs_inv_sub_inv_apply_le {A B : Matrix ι ι ℝ} {L d : ℝ}
    (hA : IsUnit A) (hB : IsUnit B)
    (hL : 0 ≤ L) (hd : 0 ≤ d) (ha : ∀ i j, |A⁻¹ i j| ≤ L) (hb : ∀ i j, |B⁻¹ i j| ≤ L)
    (hab : ∀ i j, |A i j - B i j| ≤ d) (i j : ι) :
    |A⁻¹ i j - B⁻¹ i j| ≤ (Fintype.card ι : ℝ) ^ 2 * L ^ 2 * d := by
  classical
  have hi : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := Matrix.inv_sub_inv ⟨fun _ => hB, fun _ => hA⟩
  calc
    |A⁻¹ i j - B⁻¹ i j| = |∑ k : ι, ∑ l : ι, A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      rw [← Matrix.sub_apply, hi]
      simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
    _ ≤ ∑ k : ι, ∑ l : ι, |A⁻¹ i l * (B l k - A l k) * B⁻¹ k j| := by
      exact
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _k : ι, ∑ _l : ι, L * d * L := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul, abs_mul, abs_sub_comm (B l k) (A l k)]
      exact
        mul_le_mul (mul_le_mul (ha i l) (hab l k) (abs_nonneg _) hL) (hb k j) (abs_nonneg _)
          (mul_nonneg hL hd)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/--
If a field `P` of invertible matrices has `(C, r)`-Hölder entries and inverse entries bounded by
`L`, every entry of
`P⁻¹` is `(n² L² C, r)`-Hölder; the constant is fixed before the entries and the points. -/
theorem holderWith_matrix_inv_entries {X : Type*} [PseudoMetricSpace X] (P : X → Matrix ι ι ℝ)
    (C r L : ℝ≥0) (hP : ∀ x, IsUnit (P x)) (hb : ∀ x i j, |(P x)⁻¹ i j| ≤ L)
    (hc : ∀ i j, HolderWith C r (fun x => P x i j)) (i j : ι) :
    HolderWith ((Fintype.card ι : ℝ≥0) ^ 2 * L ^ 2 * C) r (fun x => (P x)⁻¹ i j) := by
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le ?_)
  intro x _ y _
  have h :=
    Matrix.abs_inv_sub_inv_apply_le (hP x) (hP y) L.coe_nonneg
      (mul_nonneg C.coe_nonneg (Real.rpow_nonneg dist_nonneg _)) (hb x) (hb y)
      (fun a b => by simpa only [Real.dist_eq] using (hc a b).dist_le x y) i j
  simpa only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, mul_assoc] using
    h

omit [Fintype ι] [DecidableEq ι] in
/--
For `t ∈ [0, 1]`, the entries of `(1 − t) P + t Q` are `(C, r)`-Hölder when those of `P` and `Q`
are. -/
theorem holderWith_one_sub_smul_add_smul_matrix_entries (P Q : X → Matrix ι ι ℝ) (C r : ℝ≥0)
    (hP : ∀ i j, HolderWith C r (fun x => P x i j))
    (hQ : ∀ i j, HolderWith C r (fun x => Q x i j)) {t : ℝ} (ht : t ∈ Icc 0 1) (i j : ι) :
    HolderWith C r (fun x => ((1 - t) • P x + t • Q x) i j) := by
  have h := ((hP i j).smul (1 - t)).add ((hQ i j).smul t)
  have heq : C * ‖1 - t‖₊ + C * ‖t‖₊ = C := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    ring
  rw [heq] at h
  convert h using 1
  funext x
  simp only [Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply]

end InverseHolder
