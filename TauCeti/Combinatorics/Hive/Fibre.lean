/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import TauCeti.Combinatorics.Hive.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Fixed-boundary hive polytopes, properness, and finite integer fibres

Fixing the clockwise edge-difference boundary `B : Fin 3 → Fin n → R` of a normalized hive cuts out
a bounded slice of the hive cone. Summing unit-rhombus inequalities across any `(y, z)`-aligned
parallelogram inside `Δₙ` gives `f(y₀, z₀) + f(y₁, z₁) ≤ f(y₁, z₀) + f(y₀, z₁)`
(`TauCeti.Hive.IsRhombusConcave.parallelogram_le`). Evaluating on two boundary-anchored
parallelograms traps every entry `h p` between explicit linear combinations `entryLowerBound` and
`entryUpperBound` of the boundary differences, yielding four consequences:

1. **Zero-boundary uniqueness** (`TauCeti.Hive.boundary_eq_zero_iff`): the only normalized hive
   with zero boundary over any partially ordered abelian group is `0`.
2. **Matrix presentations** (`TauCeti.Hive.eqMatrix`, `TauCeti.Hive.rhombusMatrix`,
   `TauCeti.Hive.mem_fixedBoundary_iff_mulVec`, `TauCeti.Hive.exists_boundary_eq_iff_mulVec`):
   `eqMatrix R n` and `rhombusMatrix R n` are defined over any ring `R` by base change from `ℤ`
   (`TauCeti.Hive.map_intCast_eqMatrix`, `TauCeti.Hive.map_intCast_rhombusMatrix`), and over any
   partially ordered ring `R` with order-compatible addition (`[IsOrderedAddMonoid R]`, in
   particular `ℤ`, `ℚ`, `ℝ`), fixed-boundary hives are characterized as the solutions of
   `eqMatrix R n *ᵥ f = eqRHS B` and `rhombusMatrix R n *ᵥ f ≤ 0`; a hive with boundary `B` exists
   exactly when this system is feasible.
3. **Compact real polytopes and proper boundary projection** (`TauCeti.Hive.properCone`,
   `TauCeti.Hive.isConvexPolyhedron_realFibre`, `TauCeti.Hive.isCompact_realFibre`,
   `TauCeti.Hive.isProperMap_boundary_properCone`): `‖f‖ ≤ 3 * n * ‖boundaryLinear ℝ n ℝ f‖` makes
   every real fibre a compact convex polyhedron and boundary projection proper onto its closed
   range.
4. **Finite integer fibres, `hiveCount`, and finite output support**
   (`TauCeti.Hive.FixedIntegerHive`, `TauCeti.Hive.finite_fixedIntegerHive`,
   `TauCeti.Hive.hiveCount`, `TauCeti.Hive.dominates_add_of_productBoundary`,
   `TauCeti.Hive.detShift_le_of_productBoundary`,
   `TauCeti.Hive.finite_support_hiveCount_productBoundary`): bounding-box enumeration gives a
   computable `Fintype`, while degree conservation, `(λ + μ).Dominates γ`, and `λₙ + μₙ ≤ γₙ`
   confine nonempty fibres for fixed `λ, μ` to finitely many output weights `γ`.

## Main definitions

* `TauCeti.Hive.entryLowerBound`, `TauCeti.Hive.entryUpperBound`: linear boundary entry bounds.
* `TauCeti.Hive.EqConstraintIndex`, `TauCeti.Hive.eqMatrix`, `TauCeti.Hive.eqRHS`,
  `TauCeti.Hive.rhombusMatrix`: finite equality and inequality matrices over any ring.
* `TauCeti.Hive.properCone`, `TauCeti.Hive.realFibre`: closed real hive cone and polytope fibres.
* `TauCeti.Hive.FixedIntegerHive`, `TauCeti.Hive.hiveCount`,
  `TauCeti.Hive.fixedIntegerHiveRotateEquiv`, `TauCeti.Hive.rotateRotateEquiv`:
  integer hive fibres, counts, and boundary-rotation equivalences.

## Main results

* `TauCeti.Hive.IsRhombusConcave.parallelogram_le`, `TauCeti.Hive.entryLowerBound_le`,
  `TauCeti.Hive.le_entryUpperBound`, `TauCeti.Hive.boundary_eq_zero_iff`.
* `TauCeti.Hive.isConvexPolyhedron_realFibre`, `TauCeti.Hive.isCompact_realFibre`,
  `TauCeti.Hive.isProperMap_boundary_properCone`.
* `TauCeti.Hive.finite_fixedIntegerHive`, `TauCeti.Hive.shiftProductBoundaryEquiv`,
  `TauCeti.Hive.hiveCount_productBoundary_shift`, `TauCeti.Hive.dominates_add_of_productBoundary`,
  `TauCeti.Hive.detShift_le_of_productBoundary`,
  `TauCeti.Hive.finite_support_hiveCount_productBoundary`.
* `TauCeti.Hive.hiveCount_two_std_dual_trivial`, `TauCeti.Hive.hiveCount_two_std_dual_adjoint`,
  `TauCeti.Hive.hiveCount_two_std_dual_excluded`,
  `TauCeti.Hive.hiveCount_three_two_one_two_one_three_two_one`: concrete signed rank-`2` and
  multiplicity-`2` rank-`3` hive-count checks.

## References

* A. Knutson and T. Tao, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor products I:
  proof of the saturation conjecture*, J. Amer. Math. Soc. **12** (1999), 1055–1090, Appendix 2.
* A. Knutson, T. Tao, and C. Woodward, *The honeycomb model of $\mathrm{GL}_n(\mathbb{C})$ tensor
  products II*, J. Amer. Math. Soc. **17** (2004), 19–48, §5, Lemma 9.
* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §4, Lemma 1.
-/

public section

open scoped BigOperators Matrix

namespace TauCeti.Hive

/-! ### Parallelogram inequality in the `(y, z)` chart -/

section Parallelogram

variable {n : ℕ} {R : Type*} [AddCommGroup R] [PartialOrder R] [IsOrderedAddMonoid R]

private theorem strip_parallelogram_le {f : Vertex n → R} (hf : IsRhombusConcave f)
    (y₀ k z : ℕ) (h : (y₀ + k) + (z + 1) ≤ n) :
    f (Vertex.ofYZ n y₀ z (by omega)) + f (Vertex.ofYZ n (y₀ + k) (z + 1) h) ≤
      f (Vertex.ofYZ n (y₀ + k) z (by omega)) + f (Vertex.ofYZ n y₀ (z + 1) (by omega)) := by
  induction k with
  | zero =>
    rw [show Vertex.ofYZ n (y₀ + 0) (z + 1) h = Vertex.ofYZ n y₀ (z + 1) (by omega) from
        Vertex.ofYZ_eq_iff.mpr ⟨Nat.add_zero y₀, rfl⟩,
      show Vertex.ofYZ n (y₀ + 0) z _ = Vertex.ofYZ n y₀ z (by omega) from
        Vertex.ofYZ_eq_iff.mpr ⟨Nat.add_zero y₀, rfl⟩]
  | succ m ih =>
    have hprev := ih (by omega)
    have hcell := (isRhombusConcave_def f).mp hf
      (isRhombus_ofYZ_step (n := n) (y := y₀ + m) (z := z) (by omega))
    rw [show Vertex.ofYZ n (y₀ + (m + 1)) z _ = Vertex.ofYZ n (y₀ + m + 1) z (by omega) from
      Vertex.ofYZ_eq_iff.mpr ⟨by omega, rfl⟩,
      show Vertex.ofYZ n (y₀ + (m + 1)) (z + 1) h = Vertex.ofYZ n (y₀ + m + 1) (z + 1) (by omega)
        from Vertex.ofYZ_eq_iff.mpr ⟨by omega, rfl⟩]
    refine le_of_add_le_add_right (a := f (Vertex.ofYZ n (y₀ + m) z (by omega)) +
        f (Vertex.ofYZ n (y₀ + m) (z + 1) (by omega))) ?_
    calc _ = (f (Vertex.ofYZ n y₀ z (by omega)) + f (Vertex.ofYZ n (y₀ + m) (z + 1) (by omega))) +
          (f (Vertex.ofYZ n (y₀ + m) z (by omega)) +
            f (Vertex.ofYZ n (y₀ + m + 1) (z + 1) (by omega))) := by abel
      _ ≤ _ := add_le_add hprev hcell
      _ = _ := by abel

private theorem rect_parallelogram_le {f : Vertex n → R} (hf : IsRhombusConcave f)
    (y₀ y₁ z₀ l : ℕ) (hy : y₀ ≤ y₁) (h : y₁ + (z₀ + l) ≤ n) :
    f (Vertex.ofYZ n y₀ z₀ (by omega)) + f (Vertex.ofYZ n y₁ (z₀ + l) h) ≤
      f (Vertex.ofYZ n y₁ z₀ (by omega)) + f (Vertex.ofYZ n y₀ (z₀ + l) (by omega)) := by
  induction l with
  | zero =>
    rw [show Vertex.ofYZ n y₁ (z₀ + 0) h = Vertex.ofYZ n y₁ z₀ (by omega) from
        Vertex.ofYZ_eq_iff.mpr ⟨rfl, Nat.add_zero z₀⟩,
      show Vertex.ofYZ n y₀ (z₀ + 0) _ = Vertex.ofYZ n y₀ z₀ (by omega) from
        Vertex.ofYZ_eq_iff.mpr ⟨rfl, Nat.add_zero z₀⟩, add_comm (f (Vertex.ofYZ n y₁ z₀ _))]
  | succ m ih =>
    have hprev := ih (by omega)
    have hy01 : y₀ + (y₁ - y₀) = y₁ := Nat.add_sub_of_le hy
    have hstrip := strip_parallelogram_le hf y₀ (y₁ - y₀) (z₀ + m) (by omega)
    rw [show Vertex.ofYZ n (y₀ + (y₁ - y₀)) (z₀ + m + 1) _ = Vertex.ofYZ n y₁ (z₀ + (m + 1)) h from
      Vertex.ofYZ_eq_iff.mpr ⟨hy01, by omega⟩,
      show Vertex.ofYZ n (y₀ + (y₁ - y₀)) (z₀ + m) _ = Vertex.ofYZ n y₁ (z₀ + m) (by omega) from
        Vertex.ofYZ_eq_iff.mpr ⟨hy01, rfl⟩,
      show Vertex.ofYZ n y₀ (z₀ + m + 1) _ = Vertex.ofYZ n y₀ (z₀ + (m + 1)) (by omega) from
        Vertex.ofYZ_eq_iff.mpr ⟨rfl, by omega⟩] at hstrip
    refine le_of_add_le_add_right (a := f (Vertex.ofYZ n y₀ (z₀ + m) (by omega)) +
        f (Vertex.ofYZ n y₁ (z₀ + m) (by omega))) ?_
    calc _ = (f (Vertex.ofYZ n y₀ z₀ (by omega)) + f (Vertex.ofYZ n y₁ (z₀ + m) (by omega))) +
          (f (Vertex.ofYZ n y₀ (z₀ + m) (by omega)) +
            f (Vertex.ofYZ n y₁ (z₀ + (m + 1)) h)) := by abel
      _ ≤ _ := add_le_add hprev hstrip
      _ = _ := by abel

/-- **Parallelogram inequality** for rhombus-concave functions on `[y₀, y₁] × [z₀, z₁]`. -/
theorem IsRhombusConcave.parallelogram_le {f : Vertex n → R} (hf : IsRhombusConcave f)
    {y₀ y₁ z₀ z₁ : ℕ} (hy : y₀ ≤ y₁) (hz : z₀ ≤ z₁) (hsum : y₁ + z₁ ≤ n) :
    f (Vertex.ofYZ n y₀ z₀ (by omega)) + f (Vertex.ofYZ n y₁ z₁ hsum) ≤
      f (Vertex.ofYZ n y₁ z₀ (by omega)) + f (Vertex.ofYZ n y₀ z₁ (by omega)) := by
  have h := rect_parallelogram_le hf y₀ y₁ z₀ (z₁ - z₀) hy (by omega)
  rwa [Vertex.ofYZ_eq_iff.mpr ⟨rfl, Nat.add_sub_of_le hz⟩,
    show Vertex.ofYZ n y₀ (z₀ + (z₁ - z₀)) _ = Vertex.ofYZ n y₀ z₁ (by omega) from
      Vertex.ofYZ_eq_iff.mpr ⟨rfl, Nat.add_sub_of_le hz⟩] at h

/-- Parallelogram inequality specialized to a normalized `Hive`. -/
theorem parallelogram_le (h : Hive n R) {y₀ y₁ z₀ z₁ : ℕ} (hy : y₀ ≤ y₁) (hz : z₀ ≤ z₁)
    (hsum : y₁ + z₁ ≤ n) :
    h (Vertex.ofYZ n y₀ z₀ (by omega)) + h (Vertex.ofYZ n y₁ z₁ hsum) ≤
      h (Vertex.ofYZ n y₁ z₀ (by omega)) + h (Vertex.ofYZ n y₀ z₁ (by omega)) :=
  h.isRhombusConcave.parallelogram_le hy hz hsum

/-! ### Explicit two-sided entry bounds and zero-boundary uniqueness -/

/-- Explicit linear lower bound on `h p` from the parallelogram `[p.y, n - p.z] × [0, p.z]`. -/
def entryLowerBound {n : ℕ} {R : Type*} [AddCommGroup R] (B : Fin 3 → Fin n → R)
    (p : Vertex n) : R :=
  (∑ i : Fin n with i.val < p.y, B 0 i) + (∑ i : Fin n with n - p.z ≤ i.val, B 0 i) +
    ∑ i : Fin n with i.val < p.z, B 1 i

/-- Explicit linear upper bound on `h p` from the parallelogram `[0, p.y] × [0, p.z]`. -/
def entryUpperBound {n : ℕ} {R : Type*} [AddCommGroup R] (B : Fin 3 → Fin n → R)
    (p : Vertex n) : R :=
  (∑ i : Fin n with i.val < p.y, B 0 i) - ∑ i : Fin n with n - p.z ≤ i.val, B 2 i

@[simp] theorem entryLowerBound_zero {n : ℕ} {R : Type*} [AddCommGroup R] (p : Vertex n) :
    entryLowerBound (0 : Fin 3 → Fin n → R) p = 0 := by simp [entryLowerBound]

@[simp] theorem entryUpperBound_zero {n : ℕ} {R : Type*} [AddCommGroup R] (p : Vertex n) :
    entryUpperBound (0 : Fin 3 → Fin n → R) p = 0 := by simp [entryUpperBound]

/-- Every entry `h p` of a normalized hive is bounded below by `entryLowerBound h.boundary p`. -/
theorem entryLowerBound_le (h : Hive n R) (p : Vertex n) : entryLowerBound h.boundary p ≤ h p := by
  have hp := p.sum_eq
  have hpar := h.parallelogram_le (y₀ := p.y) (y₁ := n - p.z) (z₀ := 0) (z₁ := p.z)
    (by omega) (Nat.zero_le p.z) (by omega)
  rw [Vertex.ofYZ_y_z p, Vertex.ofYZ_zero_right n p.y (by omega),
    Vertex.ofYZ_sub_left n p.z (by omega), Vertex.ofYZ_zero_right n (n - p.z) (by omega),
    h.apply_edgePoint_zero, h.apply_edgePoint_one, h.apply_edgePoint_zero] at hpar
  simp only at hpar
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin n => i.val < n - p.z) (h.boundary 0)] at hpar
  simp only [not_lt] at hpar
  set s_lt := ∑ i : Fin n with i.val < n - p.z, h.boundary 0 i
  refine le_of_add_le_add_right (a := s_lt) ?_
  calc entryLowerBound h.boundary p + s_lt
      = (∑ i : Fin n with i.val < p.y, h.boundary 0 i) +
          ((s_lt + ∑ i : Fin n with n - p.z ≤ i.val, h.boundary 0 i) +
            ∑ i : Fin n with i.val < p.z, h.boundary 1 i) := by unfold entryLowerBound; abel
    _ ≤ s_lt + h p := hpar
    _ = h p + s_lt := add_comm _ _

/-- Every entry `h p` of a normalized hive is bounded above by `entryUpperBound h.boundary p`. -/
theorem le_entryUpperBound (h : Hive n R) (p : Vertex n) : h p ≤ entryUpperBound h.boundary p := by
  have hp := p.sum_eq
  have hpar := h.parallelogram_le (y₀ := 0) (y₁ := p.y) (z₀ := 0) (z₁ := p.z)
    (Nat.zero_le p.y) (Nat.zero_le p.z) (by omega)
  rwa [Vertex.ofYZ_zero_zero, h.apply_cornerA, zero_add, Vertex.ofYZ_y_z p,
    Vertex.ofYZ_zero_right n p.y (by omega), Vertex.ofYZ_zero_left n p.z (by omega),
    h.apply_edgePoint_zero, h.apply_edgePoint_two, ← sub_eq_add_neg] at hpar

/-- **Zero-boundary uniqueness**: a normalized hive has zero boundary iff it is `0`. -/
@[simp] theorem boundary_eq_zero_iff (h : Hive n R) : h.boundary = 0 ↔ h = 0 := by
  refine ⟨fun hb => ext fun p => le_antisymm ?_ ?_, fun h0 => by rw [h0, boundary_zero]⟩
  · simpa [hb] using le_entryUpperBound h p
  · simpa [hb] using entryLowerBound_le h p

end Parallelogram

/-! ### Equality and inequality matrix presentations over rings -/

section MatrixPresentation

/-- Row index type for linear equality constraints of a fixed-boundary hive. -/
abbrev EqConstraintIndex (n : ℕ) : Type := Unit ⊕ (Fin 3 × Fin n)

/-- Equality constraint matrix over a ring `R` for normalized hives with prescribed boundary. -/
def eqMatrix (R : Type*) [Ring R] (n : ℕ) : Matrix (EqConstraintIndex n) (Vertex n) R
  | Sum.inl () => Pi.single (Vertex.cornerA n) 1
  | Sum.inr (s, i) =>
      Pi.single (Vertex.edgePoint n s i.succ) 1 - Pi.single (Vertex.edgePoint n s i.castSucc) 1

/-- Right-hand side vector `(0, B)` paired with `eqMatrix R n`. -/
def eqRHS {R : Type*} [Zero R] {n : ℕ} (B : Fin 3 → Fin n → R) : EqConstraintIndex n → R
  | Sum.inl () => 0
  | Sum.inr (s, i) => B s i

@[simp] theorem eqRHS_inl {R : Type*} [Zero R] {n : ℕ} (B : Fin 3 → Fin n → R) (u : Unit) :
    eqRHS B (Sum.inl u) = 0 := (rfl)

@[simp] theorem eqRHS_inr {R : Type*} [Zero R] {n : ℕ} (B : Fin 3 → Fin n → R) (s : Fin 3)
    (i : Fin n) : eqRHS B (Sum.inr (s, i)) = B s i := (rfl)

/-- Inequality constraint matrix over `R` encoding `f b + f d - (f a + f c) ≤ 0` on `Rhombus n`. -/
def rhombusMatrix (R : Type*) [Ring R] (n : ℕ) : Matrix (Rhombus n) (Vertex n) R :=
  fun r => Pi.single r.val.2.1 1 + Pi.single r.val.2.2.2 1 -
    (Pi.single r.val.1 1 + Pi.single r.val.2.2.1 1)

@[simp] theorem eqMatrix_mulVec_inl {n : ℕ} {R : Type*} [Ring R] (f : Vertex n → R) :
    (eqMatrix R n *ᵥ f) (Sum.inl ()) = f (Vertex.cornerA n) :=
  single_one_dotProduct (Vertex.cornerA n) f

@[simp] theorem eqMatrix_mulVec_inr {n : ℕ} {R : Type*} [Ring R] (f : Vertex n → R)
    (s : Fin 3) (i : Fin n) :
    (eqMatrix R n *ᵥ f) (Sum.inr (s, i)) = boundaryLinear ℤ n R f s i := by
  simp only [Matrix.mulVec, eqMatrix, sub_dotProduct, single_one_dotProduct, boundaryLinear_apply]

@[simp] theorem rhombusMatrix_mulVec_apply {n : ℕ} {R : Type*} [Ring R] (f : Vertex n → R)
    (r : Rhombus n) :
    (rhombusMatrix R n *ᵥ f) r = -rhombusSlack f r.val.1 r.val.2.1 r.val.2.2.1 r.val.2.2.2 := by
  simp only [Matrix.mulVec, rhombusMatrix, sub_dotProduct, add_dotProduct, single_one_dotProduct,
    rhombusSlack_def]
  abel

/-- The inequalities `rhombusMatrix R n *ᵥ f ≤ 0` say exactly that `f` is rhombus-concave. -/
theorem rhombusMatrix_mulVec_nonpos_iff {n : ℕ} {R : Type*} [Ring R] [PartialOrder R]
    [IsOrderedAddMonoid R] {f : Vertex n → R} :
    rhombusMatrix R n *ᵥ f ≤ 0 ↔ IsRhombusConcave f := by
  rw [isRhombusConcave_iff_rhombusSlack_nonneg]
  exact ⟨fun hf a b c d hr => by simpa using hf ⟨(a, b, c, d), hr⟩,
    fun hf r => by simpa using hf r.property⟩

/-- Over any ring `R`, `eqMatrix R n` is the base change of `eqMatrix ℤ n`. -/
@[simp] theorem map_intCast_eqMatrix (R : Type*) [Ring R] (n : ℕ) :
    (eqMatrix ℤ n).map (Int.cast : ℤ → R) = eqMatrix R n := by
  ext idx q; rcases idx with ⟨⟨⟩⟩ | ⟨s, i⟩ <;> simp [eqMatrix, Pi.single_apply]

/-- Over any ring `R`, `rhombusMatrix R n` is the base change of `rhombusMatrix ℤ n`. -/
@[simp] theorem map_intCast_rhombusMatrix (R : Type*) [Ring R] (n : ℕ) :
    (rhombusMatrix ℤ n).map (Int.cast : ℤ → R) = rhombusMatrix R n := by
  ext r q; simp [rhombusMatrix, Pi.single_apply]

/-- Matrix characterization of fixed-boundary normalized hives over any partially ordered ring with
order-compatible addition. -/
theorem mem_fixedBoundary_iff_mulVec {n : ℕ} {R : Type*} [Ring R] [PartialOrder R]
    [IsOrderedAddMonoid R] (B : Fin 3 → Fin n → R) (f : Vertex n → R) :
    (f (Vertex.cornerA n) = 0 ∧ IsRhombusConcave f ∧ boundaryLinear ℤ n R f = B) ↔
      eqMatrix R n *ᵥ f = eqRHS B ∧ rhombusMatrix R n *ᵥ f ≤ 0 := by
  rw [rhombusMatrix_mulVec_nonpos_iff]
  exact ⟨fun ⟨hA, hconc, hB⟩ => ⟨by ext (⟨⟨⟩⟩ | ⟨s, i⟩) <;> simp [hA, ← hB], hconc⟩,
    fun ⟨heq, hconc⟩ => ⟨by simpa using congrFun heq (Sum.inl ()), hconc,
      by ext s i; simpa using congrFun heq (Sum.inr (s, i))⟩⟩

/-- A hive with boundary `B` exists exactly when the matrix system of
`TauCeti.Hive.mem_fixedBoundary_iff_mulVec` is feasible. -/
theorem exists_boundary_eq_iff_mulVec {n : ℕ} {R : Type*} [Ring R] [PartialOrder R]
    [IsOrderedAddMonoid R] (B : Fin 3 → Fin n → R) :
    (∃ h : Hive n R, h.boundary = B) ↔
      ∃ f, rhombusMatrix R n *ᵥ f ≤ 0 ∧ eqMatrix R n *ᵥ f = eqRHS B := by
  refine ⟨fun ⟨h, hB⟩ => ⟨h, ((mem_fixedBoundary_iff_mulVec B h).mp
    ⟨h.apply_cornerA, h.isRhombusConcave, (boundaryLinear_coe ℤ h).trans hB⟩).symm⟩,
    fun ⟨f, hR, hE⟩ => ?_⟩
  obtain ⟨hA, hconc, hB⟩ := (mem_fixedBoundary_iff_mulVec B f).mpr ⟨hE, hR⟩
  exact ⟨⟨f, hA, fun hr => (isRhombusConcave_def f).mp hconc hr⟩, (boundary_def _).trans hB⟩

end MatrixPresentation

/-! ### Real polyhedral cone, compact fixed-boundary polytopes, and properness -/

section RealPolyhedron

private def evalCLM {n : ℕ} (p : Vertex n) : (Vertex n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj p

@[simp] private theorem evalCLM_apply {n : ℕ} (p : Vertex n) (f : Vertex n → ℝ) :
    evalCLM p f = f p := (rfl)

/-- The pointed cone of normalized real hives is a `TauCeti.IsConvexPolyhedron`. -/
theorem isConvexPolyhedron_pointedCone (n : ℕ) :
    IsConvexPolyhedron (pointedCone ℝ n : Set (Vertex n → ℝ)) := by
  let g : Bool ⊕ Rhombus n → ((Vertex n → ℝ) →ᴬ[ℝ] ℝ)
    | Sum.inl true => (evalCLM (Vertex.cornerA n)).toContinuousAffineMap
    | Sum.inl false => (-evalCLM (Vertex.cornerA n)).toContinuousAffineMap
    | Sum.inr r => (evalCLM r.val.2.1 + evalCLM r.val.2.2.2 -
        (evalCLM r.val.1 + evalCLM r.val.2.2.1)).toContinuousAffineMap
  have heq : (pointedCone ℝ n : Set (Vertex n → ℝ)) = {f | ∀ i, g i f ≤ 0} := by
    ext f; simp only [SetLike.mem_coe, mem_pointedCone_iff, Set.mem_ofPred_eq, Sum.forall,
      Bool.forall_bool]
    refine ⟨fun ⟨hA, hconc⟩ => ⟨⟨by simp [g, hA], by simp [g, hA]⟩, fun r => ?_⟩,
      fun ⟨⟨hneg, hpos⟩, hr⟩ => ⟨le_antisymm (by simpa [g] using hpos) (by simpa [g] using hneg),
        (isRhombusConcave_def f).mpr fun a b c d hrh => ?_⟩⟩
    · simpa [g, sub_nonpos] using (isRhombusConcave_def f).mp hconc r.property
    · simpa [g, sub_nonpos] using hr ⟨(a, b, c, d), hrh⟩
  exact heq ▸ isConvexPolyhedron_setOf_forall g

/-- The closed convex cone of normalized real hives packaged as a `ProperCone`. -/
def properCone (n : ℕ) : ProperCone ℝ (Vertex n → ℝ) where
  toSubmodule := pointedCone ℝ n
  isClosed' := (isConvexPolyhedron_pointedCone n).isClosed

@[simp] theorem mem_properCone_iff {n : ℕ} {f : Vertex n → ℝ} :
    f ∈ properCone n ↔ f ∈ pointedCone ℝ n := Iff.rfl

@[simp] theorem coe_properCone (n : ℕ) :
    (properCone n : Set (Vertex n → ℝ)) = (pointedCone ℝ n : Set (Vertex n → ℝ)) := (rfl)

/-- The real fixed-boundary hive polytope inside `Vertex n → ℝ`. -/
def realFibre {n : ℕ} (B : Fin 3 → Fin n → ℝ) : Set (Vertex n → ℝ) :=
  {f ∈ pointedCone ℝ n | boundaryLinear ℝ n ℝ f = B}

theorem mem_realFibre_iff {n : ℕ} {B : Fin 3 → Fin n → ℝ} {f : Vertex n → ℝ} :
    f ∈ realFibre B ↔ ∃ h : RealHive n, ⇑h = f ∧ h.boundary = B := by
  simp only [realFibre, Set.mem_ofPred_eq, mem_pointedCone_iff]
  refine ⟨fun ⟨⟨hA, hconc⟩, hB⟩ => ?_, fun ⟨h, hf, hB⟩ => ?_⟩
  · let h : RealHive n := ⟨f, hA, fun hr => (isRhombusConcave_def f).mp hconc hr⟩
    exact ⟨h, rfl, (boundaryLinear_coe ℝ h).symm.trans hB⟩
  · subst hf; exact ⟨⟨h.apply_cornerA, h.isRhombusConcave⟩, (boundaryLinear_coe ℝ h).trans hB⟩

/-- Every real fixed-boundary hive fibre is a `TauCeti.IsConvexPolyhedron`. -/
theorem isConvexPolyhedron_realFibre {n : ℕ} (B : Fin 3 → Fin n → ℝ) :
    IsConvexPolyhedron (realFibre B) := by
  let edgeDiff (s : Fin 3) (i : Fin n) : (Vertex n → ℝ) →ᴬ[ℝ] ℝ :=
    (evalCLM (Vertex.edgePoint n s i.succ) -
      evalCLM (Vertex.edgePoint n s i.castSucc)).toContinuousAffineMap
  let g : Bool × Fin 3 × Fin n → ((Vertex n → ℝ) →ᴬ[ℝ] ℝ)
    | (true, s, i) => edgeDiff s i - ContinuousAffineMap.const ℝ (Vertex n → ℝ) (B s i)
    | (false, s, i) => ContinuousAffineMap.const ℝ (Vertex n → ℝ) (B s i) - edgeDiff s i
  have heq : realFibre B =
      (pointedCone ℝ n : Set (Vertex n → ℝ)) ∩ {f | ∀ p, g p f ≤ 0} := by
    ext f; simp only [realFibre, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, Prod.forall,
      Bool.forall_bool]
    refine and_congr_right fun _ =>
      ⟨fun hB => ⟨fun s i => by simp [g, edgeDiff, ← hB], fun s i => by simp [g, edgeDiff, ← hB]⟩,
        fun ⟨h1, h2⟩ => funext fun s => funext fun i => le_antisymm
          (by simpa [g, edgeDiff, sub_nonpos] using h2 s i)
          (by simpa [g, edgeDiff, sub_nonpos] using h1 s i)⟩
  exact heq ▸ (isConvexPolyhedron_pointedCone n).inter (isConvexPolyhedron_setOf_forall g)

/-- Uniform linear norm bound `‖f‖ ≤ 3 * n * ‖boundaryLinear ℝ n ℝ f‖` on the real hive cone. -/
theorem norm_le_three_mul_norm_boundary {n : ℕ} {f : Vertex n → ℝ} (hf : f ∈ pointedCone ℝ n) :
    ‖f‖ ≤ 3 * n * ‖boundaryLinear ℝ n ℝ f‖ := by
  set B := boundaryLinear ℝ n ℝ f
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro p
  obtain ⟨hA, hconc⟩ := mem_pointedCone_iff.mp hf
  let h : RealHive n := ⟨f, hA, fun hr => (isRhombusConcave_def f).mp hconc hr⟩
  have hB_eq : h.boundary = B := (boundaryLinear_coe ℝ h).symm
  have hlo : entryLowerBound B p ≤ f p := by simpa [hB_eq, h] using entryLowerBound_le h p
  have hhi : f p ≤ entryUpperBound B p := by simpa [hB_eq, h] using le_entryUpperBound h p
  have hite (P : Prop) [Decidable P] (s : Fin 3) (i : Fin n) :
      ‖if P then B s i else 0‖ ≤ ‖B‖ := by
    split_ifs
    · exact (norm_le_pi_norm (B s) i).trans (norm_le_pi_norm B s)
    · simp
  have hlo_norm : ‖entryLowerBound B p‖ ≤ 3 * n * ‖B‖ := by
    rw [entryLowerBound, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine (norm_sum_le_of_le Finset.univ (n := fun _ => 3 * ‖B‖) fun i _ => ?_).trans_eq
      (by simp; ring)
    have htri := (norm_add_le
      ((if i.val < p.y then B 0 i else 0) + if n - p.z ≤ i.val then B 0 i else 0)
      (if i.val < p.z then B 1 i else 0)).trans (add_le_add (norm_add_le _ _) le_rfl)
    linarith [hite (i.val < p.y) 0 i, hite (n - p.z ≤ i.val) 0 i, hite (i.val < p.z) 1 i]
  have hhi_norm : ‖entryUpperBound B p‖ ≤ 3 * n * ‖B‖ := by
    rw [entryUpperBound, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine (norm_sum_le_of_le Finset.univ (n := fun _ => 3 * ‖B‖) fun i _ => ?_).trans_eq
      (by simp; ring)
    linarith [norm_sub_le (if i.val < p.y then B 0 i else 0)
      (if n - p.z ≤ i.val then B 2 i else 0), hite (i.val < p.y) 0 i,
      hite (n - p.z ≤ i.val) 2 i, norm_nonneg B]
  rw [Real.norm_eq_abs] at hlo_norm hhi_norm ⊢
  exact abs_le.mpr ⟨by linarith [neg_le_of_abs_le hlo_norm], by linarith [le_of_abs_le hhi_norm]⟩

/-- Every real fixed-boundary hive fibre is bounded in `Vertex n → ℝ`. -/
theorem isBounded_realFibre {n : ℕ} (B : Fin 3 → Fin n → ℝ) :
    Bornology.IsBounded (realFibre B) :=
  isBounded_iff_forall_norm_le.mpr ⟨3 * n * ‖B‖, fun _ hf => by
    simpa [hf.2] using norm_le_three_mul_norm_boundary hf.1⟩

/-- **Every real fixed-boundary hive fibre is compact.** -/
theorem isCompact_realFibre {n : ℕ} (B : Fin 3 → Fin n → ℝ) : IsCompact (realFibre B) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨(isConvexPolyhedron_realFibre B).isClosed, isBounded_realFibre B⟩

theorem continuous_boundaryLinear (n : ℕ) : Continuous (boundaryLinear ℝ n ℝ) :=
  continuous_pi fun s => continuous_pi fun i => by
    simp only [boundaryLinear_apply]; exact (continuous_apply _).sub (continuous_apply _)

/-- **Boundary projection on the closed real hive cone is a proper map.** -/
theorem isProperMap_boundary_properCone (n : ℕ) :
    IsProperMap (fun f : properCone n => boundaryLinear ℝ n ℝ f.val) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨(continuous_boundaryLinear n).comp continuous_subtypeVal, fun K hK => ?_⟩
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  let S : Set (Vertex n → ℝ) := (properCone n : Set (Vertex n → ℝ)) ∩ boundaryLinear ℝ n ℝ ⁻¹' K
  have hS_compact : IsCompact S := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨(properCone n).isClosed.inter (hK.isClosed.preimage (continuous_boundaryLinear n)),
      isBounded_iff_forall_norm_le.mpr ⟨3 * n * max C 0, fun f hf =>
        (norm_le_three_mul_norm_boundary hf.1).trans <|
          mul_le_mul_of_nonneg_left ((hC _ hf.2).trans (le_max_left C 0)) (by positivity)⟩⟩
  have hpre : ((fun f : properCone n => boundaryLinear ℝ n ℝ f.val) ⁻¹' K) = Subtype.val ⁻¹' S := by
    ext f; exact ⟨fun h => ⟨f.property, h⟩, fun h => h.2⟩
  exact hpre ▸ (properCone n).isClosed.isProperMap_subtypeVal.isCompact_preimage hS_compact

/-- The image of the real hive cone under boundary projection is closed in `Fin 3 → Fin n → ℝ`. -/
theorem isClosed_range_boundary_properCone (n : ℕ) :
    IsClosed (Set.range fun f : properCone n => boundaryLinear ℝ n ℝ f.val) :=
  (isProperMap_boundary_properCone n).isClosed_range

end RealPolyhedron

/-! ### Finite integer fibres, `hiveCount`, output bounds, and finite output support -/

section IntegerFibre

/-- The integer hives of size `n` with prescribed clockwise cyclic boundary `B`. -/
abbrev FixedIntegerHive {n : ℕ} (B : Fin 3 → Fin n → ℤ) : Type :=
  {h : IntegerHive n // h.boundary = B}

/-- Explicit coordinate bounding-box `Finset` containing every integer hive with boundary `B`. -/
def fixedIntegerHiveBox {n : ℕ} (B : Fin 3 → Fin n → ℤ) : Finset (Vertex n → ℤ) :=
  (Fintype.piFinset fun p => Finset.Icc (entryLowerBound B p) (entryUpperBound B p)).filter
    fun f => f (Vertex.cornerA n) = 0 ∧ IsRhombusConcave f ∧ boundaryLinear ℤ n ℤ f = B

@[simp] theorem mem_fixedIntegerHiveBox_iff {n : ℕ} {B : Fin 3 → Fin n → ℤ} {f : Vertex n → ℤ} :
    f ∈ fixedIntegerHiveBox B ↔
      f (Vertex.cornerA n) = 0 ∧ IsRhombusConcave f ∧ boundaryLinear ℤ n ℤ f = B := by
  simp only [fixedIntegerHiveBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc,
    and_iff_right_iff_imp]
  rintro ⟨hA, hconc, hB⟩ p
  let h : IntegerHive n := ⟨f, hA, fun hr => (isRhombusConcave_def f).mp hconc hr⟩
  have hb : h.boundary = B := (boundaryLinear_coe ℤ h).symm.trans hB
  exact ⟨by simpa [hb, h] using entryLowerBound_le h p,
    by simpa [hb, h] using le_entryUpperBound h p⟩

/-- Computable equivalence between `FixedIntegerHive B` and `fixedIntegerHiveBox B`. -/
def fixedIntegerHiveEquivBox {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    FixedIntegerHive B ≃ ↥(fixedIntegerHiveBox B) where
  toFun h := ⟨h.val, mem_fixedIntegerHiveBox_iff.mpr
    ⟨h.val.apply_cornerA, h.val.isRhombusConcave, (boundaryLinear_coe ℤ h.val).trans h.property⟩⟩
  invFun f :=
    let hf := mem_fixedIntegerHiveBox_iff.mp f.property
    let h : IntegerHive n := ⟨f.val, hf.1, fun hr => (isRhombusConcave_def f.val).mp hf.2.1 hr⟩
    ⟨h, (boundaryLinear_coe ℤ h).symm.trans hf.2.2⟩
  left_inv _ := by ext p; rfl
  right_inv _ := by ext p; rfl

/-- Computable `Fintype` instance on `FixedIntegerHive B` from bounding-box enumeration. -/
instance instFintypeFixedIntegerHive {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    Fintype (FixedIntegerHive B) :=
  Fintype.ofEquiv ↥(fixedIntegerHiveBox B) (fixedIntegerHiveEquivBox B).symm

/-- **Every fixed-boundary fibre of integer hives is finite.** -/
theorem finite_fixedIntegerHive {n : ℕ} (B : Fin 3 → Fin n → ℤ) : Finite (FixedIntegerHive B) :=
  inferInstance

/-- The number of normalized integer hives with clockwise cyclic boundary `B`. -/
def hiveCount {n : ℕ} (B : Fin 3 → Fin n → ℤ) : ℕ := Fintype.card (FixedIntegerHive B)

@[simp] theorem card_fixedIntegerHive {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    Fintype.card (FixedIntegerHive B) = hiveCount B := (rfl)

theorem natCard_fixedIntegerHive {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    Nat.card (FixedIntegerHive B) = hiveCount B := Nat.card_eq_fintype_card

theorem hiveCount_eq_card_box {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    hiveCount B = (fixedIntegerHiveBox B).card := by
  rw [hiveCount, Fintype.card_congr (fixedIntegerHiveEquivBox B), Fintype.card_coe]

theorem hiveCount_pos_iff {n : ℕ} {B : Fin 3 → Fin n → ℤ} :
    0 < hiveCount B ↔ Nonempty (FixedIntegerHive B) := Fintype.card_pos_iff

theorem hiveCount_eq_zero_iff {n : ℕ} {B : Fin 3 → Fin n → ℤ} :
    hiveCount B = 0 ↔ IsEmpty (FixedIntegerHive B) := Fintype.card_eq_zero_iff

/-- Any boundary with nonzero cyclic trace has zero integer hives. -/
theorem hiveCount_eq_zero_of_sum_ne_zero {n : ℕ} {B : Fin 3 → Fin n → ℤ}
    (hsum : (∑ s : Fin 3, ∑ i : Fin n, B s i) ≠ 0) : hiveCount B = 0 :=
  hiveCount_eq_zero_iff.mpr ⟨fun ⟨h, hb⟩ => hsum (hb ▸ h.sum_boundary)⟩

/-- The zero boundary admits the unique normalized integer hive `0`. -/
instance uniqueFixedIntegerHiveZero (n : ℕ) :
    Unique (FixedIntegerHive (0 : Fin 3 → Fin n → ℤ)) where
  default := ⟨0, boundary_zero⟩
  uniq h := Subtype.ext ((boundary_eq_zero_iff h.val).mp h.property)

@[simp] theorem hiveCount_zero (n : ℕ) : hiveCount (0 : Fin 3 → Fin n → ℤ) = 1 :=
  Fintype.card_unique

/-- At rank `0`, the unique empty boundary has a single normalized integer hive. -/
@[simp] theorem hiveCount_rank_zero (B : Fin 3 → Fin 0 → ℤ) : hiveCount B = 1 := by
  rw [Subsingleton.elim B 0, hiveCount_zero]

/-- Clockwise boundary-shift equivalence on integer hive fibres: rotating a hive twice sends
boundary `fun s => B (s + 1)` to `B`, with `Hive.rotate` as inverse. -/
def fixedIntegerHiveRotateEquiv {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    FixedIntegerHive (fun s => B (s + 1)) ≃ FixedIntegerHive B where
  toFun h := ⟨h.val.rotate.rotate, by
    rw [boundary_rotate, boundary_rotate, h.property]
    ext s i
    have hs : s + 1 + 1 + 1 = s := by fin_cases s <;> decide
    exact congrFun (congrArg B hs) i⟩
  invFun h := ⟨h.val.rotate, by ext s i; simp [h.property]⟩
  left_inv _ := by ext p; simp
  right_inv _ := by ext p; simp

@[simp] theorem fixedIntegerHiveRotateEquiv_apply_coe {n : ℕ} (B : Fin 3 → Fin n → ℤ)
    (h : FixedIntegerHive (fun s => B (s + 1))) :
    (fixedIntegerHiveRotateEquiv B h).val = h.val.rotate.rotate := (rfl)

@[simp] theorem fixedIntegerHiveRotateEquiv_symm_apply_coe {n : ℕ} (B : Fin 3 → Fin n → ℤ)
    (h : FixedIntegerHive B) :
    ((fixedIntegerHiveRotateEquiv B).symm h).val = h.val.rotate := (rfl)

/-- Clockwise rotation of the boundary preserves `hiveCount`. -/
@[simp] theorem hiveCount_rotate {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    hiveCount (fun s => B (s + 1)) = hiveCount B :=
  Fintype.card_congr (fixedIntegerHiveRotateEquiv B)

private theorem cyclicBoundary_eq_productBoundary_add_one {n : ℕ} (lam μ ν : DominantWeight n) :
    ![lam.val, μ.val, ν.val] = fun s => productBoundary ν lam μ.dual (s + 1) := by
  ext s r; fin_cases s <;> simp

/-- Rotating twice identifies integer hives of clockwise cyclic boundary `![lam.1, μ.1, ν.1]` with
integer hives of product boundary `productBoundary ν lam μ.dual`. -/
def rotateRotateEquiv {n : ℕ} (lam μ ν : DominantWeight n) :
    FixedIntegerHive ![lam.val, μ.val, ν.val] ≃ FixedIntegerHive (productBoundary ν lam μ.dual) :=
  (Equiv.subtypeEquivRight fun _ => by
    rw [cyclicBoundary_eq_productBoundary_add_one]).trans
    (fixedIntegerHiveRotateEquiv (productBoundary ν lam μ.dual))

@[simp] theorem rotateRotateEquiv_apply_coe {n : ℕ} (lam μ ν : DominantWeight n)
    (h : FixedIntegerHive ![lam.val, μ.val, ν.val]) :
    (rotateRotateEquiv lam μ ν h).val = h.val.rotate.rotate := (rfl)

@[simp] theorem rotateRotateEquiv_symm_apply_coe {n : ℕ} (lam μ ν : DominantWeight n)
    (k : FixedIntegerHive (productBoundary ν lam μ.dual)) :
    ((rotateRotateEquiv lam μ ν).symm k).val = k.val.rotate := (rfl)

/-- Rotating twice identifies `hiveCount ![lam.1, μ.1, ν.1]` with
`hiveCount (productBoundary ν lam μ.dual)`. -/
theorem hiveCount_cyclic_eq_hiveCount_productBoundary {n : ℕ} (lam μ ν : DominantWeight n) :
    hiveCount ![lam.val, μ.val, ν.val] = hiveCount (productBoundary ν lam μ.dual) := by
  rw [cyclicBoundary_eq_productBoundary_add_one, hiveCount_rotate]

/-- Reflection of the boundary preserves `hiveCount`. -/
@[simp] theorem hiveCount_reflect {n : ℕ} (B : Fin 3 → Fin n → ℤ) :
    hiveCount (fun s i => -B s.rev i.rev) = hiveCount B :=
  Fintype.card_congr
    { toFun := fun h => ⟨h.val.reflect, by ext s i; simp [h.property]⟩
      invFun := fun h => ⟨h.val.reflect, by ext s i; simp [h.property]⟩
      left_inv := fun _ => by ext p; simp
      right_inv := fun _ => by ext p; simp }

/-- Contragredient duality symmetry `hiveCount (μ*, λ*, γ**) = hiveCount (λ, μ, γ*)`. -/
theorem hiveCount_productBoundary_dual {n : ℕ} (lam μ γ : DominantWeight n) :
    hiveCount (productBoundary μ.dual lam.dual γ.dual) = hiveCount (productBoundary lam μ γ) := by
  have hdual_pb :
      productBoundary lam.dual.dual μ.dual.dual γ.dual.dual = productBoundary lam μ γ := by
    ext s i; fin_cases s <;> simp
  exact Fintype.card_congr
    { toFun := fun h =>
        ⟨h.val.reflect.rotate, (boundary_reflect_rotate_of_productBoundary h.property).trans
            hdual_pb⟩
      invFun := fun h => ⟨h.val.reflect.rotate, boundary_reflect_rotate_of_productBoundary
          h.property⟩
      left_inv := fun _ => by ext p; simp
      right_inv := fun _ => by ext p; simp }

/-- **Determinant-shift equivalence on product-boundary hive fibres**: adding the normalized affine
hive `affine n a (a + b)` bijects `FixedIntegerHive (productBoundary lam μ γ)` with
`FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)))`. -/
def shiftProductBoundaryEquiv {n : ℕ} (lam μ γ : DominantWeight n) (a b : ℤ) :
    FixedIntegerHive (productBoundary lam μ γ) ≃
      FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))) where
  toFun h := ⟨h.val + affine n a (a + b), by ext s i; fin_cases s <;> simp [h.property]⟩
  invFun h :=
    ⟨h.val + affine n (-a) (-(a + b)), by ext s i; fin_cases s <;> simp [h.property]; omega⟩
  left_inv h := by ext p; simp [mul_add]; abel
  right_inv h := by ext p; simp [mul_add]; abel

/-- Underlying hive of the forward map `shiftProductBoundaryEquiv`. -/
@[simp] theorem shiftProductBoundaryEquiv_apply_val {n : ℕ} (lam μ γ : DominantWeight n) (a b : ℤ)
    (h : FixedIntegerHive (productBoundary lam μ γ)) :
    (shiftProductBoundaryEquiv lam μ γ a b h).val = h.val + affine n a (a + b) := (rfl)

/-- Underlying hive of the inverse map `shiftProductBoundaryEquiv.symm`. -/
@[simp] theorem shiftProductBoundaryEquiv_symm_apply_val {n : ℕ} (lam μ γ : DominantWeight n)
    (a b : ℤ) (h : FixedIntegerHive (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b)))) :
    ((shiftProductBoundaryEquiv lam μ γ a b).symm h).val = h.val + affine n (-a) (-(a + b)) := (rfl)

/-- Shifting a product boundary by determinant twists `(a, b, a + b)` preserves `hiveCount`. -/
@[simp] theorem hiveCount_productBoundary_shift {n : ℕ} (lam μ γ : DominantWeight n) (a b : ℤ) :
    hiveCount (productBoundary (lam.shift a) (μ.shift b) (γ.shift (a + b))) =
      hiveCount (productBoundary lam μ γ) :=
  (Fintype.card_congr (shiftProductBoundaryEquiv lam μ γ a b)).symm

/-- Edge step of a fixed-boundary integer hive along side `A → B` (`i = 0`) in chart coordinates. -/
theorem step_ofChart_zero_left {n : ℕ} {B : Fin 3 → Fin n → ℤ} (h : FixedIntegerHive B)
    {j : ℕ} (hj : j < n) :
    h.val (Vertex.ofChart n 0 (j + 1) (Nat.zero_le _) hj) -
        h.val (Vertex.ofChart n 0 j (Nat.zero_le _) hj.le) = B 0 ⟨j, hj⟩ := by
  have hb := congrFun (congrFun h.property 0) ⟨j, hj⟩
  rw [boundary_apply] at hb
  have h1 : Vertex.edgePoint n 0 (⟨j, hj⟩ : Fin n).succ =
      Vertex.ofChart n 0 (j + 1) (Nat.zero_le _) hj :=
    (Vertex.ofChart_zero_left n (j + 1) hj).symm
  have h2 : Vertex.edgePoint n 0 (⟨j, hj⟩ : Fin n).castSucc =
      Vertex.ofChart n 0 j (Nat.zero_le _) hj.le :=
    (Vertex.ofChart_zero_left n j hj.le).symm
  rwa [h1, h2] at hb

/-- Edge step of a fixed-boundary integer hive along side `B → C` (`j = n`) in chart coordinates. -/
theorem step_ofChart_right {n : ℕ} {B : Fin 3 → Fin n → ℤ} (h : FixedIntegerHive B)
    {i : ℕ} (hi : i < n) :
    h.val (Vertex.ofChart n (i + 1) n hi le_rfl) -
        h.val (Vertex.ofChart n i n hi.le le_rfl) = B 1 ⟨i, hi⟩ := by
  have hb := congrFun (congrFun h.property 1) ⟨i, hi⟩
  rw [boundary_apply] at hb
  have h1 : Vertex.edgePoint n 1 (⟨i, hi⟩ : Fin n).succ = Vertex.ofChart n (i + 1) n hi le_rfl :=
    (Vertex.ofChart_right n (i + 1) hi).symm
  have h2 : Vertex.edgePoint n 1 (⟨i, hi⟩ : Fin n).castSucc = Vertex.ofChart n i n hi.le le_rfl :=
    (Vertex.ofChart_right n i hi.le).symm
  rwa [h1, h2] at hb

/-- Edge step of a fixed-boundary integer hive along diagonal `A → C` (`i = j`) in chart
coordinates. -/
theorem step_ofChart_self {n : ℕ} {B : Fin 3 → Fin n → ℤ} (h : FixedIntegerHive B)
    {r : ℕ} (hr : r < n) :
    h.val (Vertex.ofChart n (r + 1) (r + 1) le_rfl hr) -
        h.val (Vertex.ofChart n r r le_rfl hr.le) = -B 2 (⟨r, hr⟩ : Fin n).rev := by
  let i : Fin n := (⟨r, hr⟩ : Fin n).rev
  have hb := congrFun (congrFun h.property 2) i
  rw [boundary_apply] at hb
  have h1 : Vertex.edgePoint n 2 i.succ = Vertex.ofChart n r r le_rfl hr.le := by
    rw [Vertex.ofChart_self]; congr 1; ext; simp [i]; omega
  have h2 : Vertex.edgePoint n 2 i.castSucc = Vertex.ofChart n (r + 1) (r + 1) le_rfl hr := by
    rw [Vertex.ofChart_self]; rfl
  rw [h1, h2] at hb
  linarith

/-- Edge step along `A → B` (`i = 0`) for an integer hive with `productBoundary lam μ γ`. -/
theorem step_ofChart_zero_left_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    (h : FixedIntegerHive (productBoundary lam μ γ)) {j : ℕ} (hj : j < n) :
    h.val (Vertex.ofChart n 0 (j + 1) (Nat.zero_le _) hj) -
        h.val (Vertex.ofChart n 0 j (Nat.zero_le _) hj.le) = lam.val ⟨j, hj⟩ := by
  simpa using step_ofChart_zero_left h hj

/-- Edge step along `B → C` (`j = n`) for an integer hive with `productBoundary lam μ γ`. -/
theorem step_ofChart_right_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    (h : FixedIntegerHive (productBoundary lam μ γ)) {i : ℕ} (hi : i < n) :
    h.val (Vertex.ofChart n (i + 1) n hi le_rfl) -
        h.val (Vertex.ofChart n i n hi.le le_rfl) = μ.val ⟨i, hi⟩ := by
  simpa using step_ofChart_right h hi

/-- Edge step along `A → C` (`i = j`) for an integer hive with `productBoundary lam μ γ`. -/
theorem step_ofChart_self_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n}
    (h : FixedIntegerHive (productBoundary lam μ γ)) {r : ℕ} (hr : r < n) :
    h.val (Vertex.ofChart n (r + 1) (r + 1) le_rfl hr) -
        h.val (Vertex.ofChart n r r le_rfl hr.le) = γ.val ⟨r, hr⟩ := by
  simpa [DominantWeight.dual_apply] using step_ofChart_self h hr

/-! ### Central-degree conservation, dominance bound, lower-coordinate bound, and finite support -/

/-- **Central-degree conservation**: `h.boundary = productBoundary lam μ γ` implies `|λ|+|μ| = |γ|`.
-/
theorem sum_eq_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) :
    (∑ i, lam.val i) + (∑ i, μ.val i) = ∑ i, γ.val i :=
  (sum_productBoundary_eq_zero_iff lam μ γ).mp (hb ▸ h.sum_boundary)

/-- Suffix-sum inequality for `productBoundary lam μ γ`: for every `k ≤ n`, the sum of the last
`n - k` coordinates of `γ` is at least the sum of those of `λ` and `μ`. -/
theorem suffix_sum_le_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) {k : ℕ} (hk : k ≤ n) :
    (∑ i : Fin n with k ≤ i.val, lam.val i) + (∑ i : Fin n with k ≤ i.val, μ.val i) ≤
      ∑ i : Fin n with k ≤ i.val, γ.val i := by
  let p : Vertex n := Vertex.edgePoint n 1 ⟨n - k, by omega⟩
  have hup := le_entryUpperBound h.rotate p
  rw [apply_edgePoint_one, Fin.val_mk] at hup; unfold entryUpperBound at hup
  rw [show p.y = k by simp [p]; omega, show n - p.z = k by simp [p]; omega,
    show h.rotate.boundary 0 = μ.val by simp [boundary_rotate, hb],
    show h.rotate.boundary 1 = γ.dual.val by simp [boundary_rotate, hb],
    show h.rotate.boundary 2 = lam.val by simp [boundary_rotate, hb]] at hup
  have hdual : (∑ i : Fin n with i.val < n - k, γ.dual.val i) = -∑ j : Fin n with k ≤ j.val, γ.val j
      :=
    by
    have hd : γ.dual.val = fun i : Fin n => -γ.val i.rev := funext γ.dual_apply
    rw [← TauCeti.prefixSum_def, hd, TauCeti.prefixSum_comp_rev (Nat.sub_le n k)
        (fun j => -γ.val j),
      Nat.sub_sub_self hk, Finset.sum_neg_distrib]
  rw [hdual, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin n => i.val < k) μ.val] at hup
  simp only [not_lt] at hup; linarith

/-- **Dominance prefix-sum bound** for `productBoundary lam μ γ`. -/
theorem prefix_sum_le_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (k : ℕ) :
    (∑ i : Fin n with i.val < k, γ.val i) ≤
      (∑ i : Fin n with i.val < k, lam.val i) + ∑ i : Fin n with i.val < k, μ.val i := by
  rcases le_or_gt k n with hk | hk
  · have hsplit (g : Fin n → ℤ) :
        (∑ i : Fin n with i.val < k, g i) + (∑ i : Fin n with k ≤ i.val, g i) = ∑ i, g i := by
      simpa [not_lt] using Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i.val < k) g
    linarith [sum_eq_of_productBoundary hb, suffix_sum_le_of_productBoundary hb hk,
      hsplit lam.val, hsplit μ.val, hsplit γ.val]
  · rw [show ({i : Fin n | i.val < k} : Finset (Fin n)) = Finset.univ by
      ext i; simp [i.isLt.trans hk], ← sum_eq_of_productBoundary hb]

/-- **Dominance bound `γ ≤ λ + μ`**: `lam + μ` dominates `γ` when `productBoundary lam μ γ` is
feasible. -/
theorem dominates_add_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) : (lam + μ).Dominates γ :=
  DominantWeight.dominates_iff.mpr
    ⟨by simp [Finset.sum_add_distrib, ← sum_eq_of_productBoundary hb],
      fun k => by simpa [Finset.sum_add_distrib] using prefix_sum_le_of_productBoundary hb k⟩

/-- **Lower-coordinate bound `γₙ ≥ λₙ + μₙ`** on nonempty weights. -/
theorem last_le_of_productBoundary {m : ℕ} {lam μ γ : DominantWeight (m + 1)}
    {h : IntegerHive (m + 1)} (hb : h.boundary = productBoundary lam μ γ) :
    lam.val (Fin.last m) + μ.val (Fin.last m) ≤ γ.val (Fin.last m) := by
  have hsuf := suffix_sum_le_of_productBoundary hb (Nat.le_succ m)
  have hlast : ({i : Fin (m + 1) | m ≤ i.val} : Finset (Fin (m + 1))) = {Fin.last m} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.ext_iff, Fin.val_last]; omega
  simpa [hlast] using hsuf

/-- Uniform determinant-twist lower bound `λ.detShift + μ.detShift ≤ γ.detShift` for all `n`. -/
theorem detShift_le_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) : lam.detShift + μ.detShift ≤ γ.detShift :=
  match n, lam, μ, γ, h, hb with
  | 0, _, _, _, _, _ => by simp
  | _ + 1, _, _, _, _, hb => last_le_of_productBoundary hb

/-- Polynomial input weights force a polynomial output weight whenever the hive fibre is nonempty.
-/
theorem isPolynomial_of_productBoundary {n : ℕ} {lam μ γ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hlam : lam.IsPolynomial) (hμ : μ.IsPolynomial) :
    γ.IsPolynomial := by
  rw [DominantWeight.isPolynomial_iff_zero_le_detShift] at hlam hμ ⊢
  linarith [detShift_le_of_productBoundary hb]

/-- Upper first-coordinate bound `γ₁ ≤ λ₁ + μ₁` on nonempty weights. -/
theorem first_le_of_productBoundary {m : ℕ} {lam μ γ : DominantWeight (m + 1)}
    {h : IntegerHive (m + 1)} (hb : h.boundary = productBoundary lam μ γ) :
    γ.val 0 ≤ lam.val 0 + μ.val 0 := by
  have hpre := prefix_sum_le_of_productBoundary hb 1
  have hzero : ({i : Fin (m + 1) | i.val < 1} : Finset (Fin (m + 1))) = {0} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.ext_iff, Fin.val_zero]; omega
  rw [hzero] at hpre; simpa using hpre

/-- **Finite output support**: for fixed `λ, μ`, only finitely many `γ` have `0 < hiveCount`. -/
theorem finite_support_hiveCount_productBoundary {n : ℕ} (lam μ : DominantWeight n) :
    {γ : DominantWeight n | 0 < hiveCount (productBoundary lam μ γ)}.Finite := by
  cases n with
  | zero => exact Set.toFinite _
  | succ m =>
    let box : Finset (Fin (m + 1) → ℤ) := Fintype.piFinset fun _ =>
      Finset.Icc (lam.val (Fin.last m) + μ.val (Fin.last m)) (lam.val 0 + μ.val 0)
    refine (box.finite_toSet.preimage Subtype.coe_injective.injOn).subset fun γ hγ => ?_
    obtain ⟨⟨h, hb⟩⟩ := hiveCount_pos_iff.mp hγ
    simp only [Set.mem_preimage, SetLike.mem_coe, box, Fintype.mem_piFinset, Finset.mem_Icc]
    exact fun j => ⟨(last_le_of_productBoundary hb).trans (γ.property (Fin.le_last j)),
      (γ.property (Fin.zero_le j)).trans (first_le_of_productBoundary hb)⟩

end IntegerFibre

/-! ### Concrete checks at ranks `2` and `3` -/

section RankChecks

instance subsingleton_fixedIntegerHive_two (B : Fin 3 → Fin 2 → ℤ) :
    Subsingleton (FixedIntegerHive B) :=
  ⟨fun h₁ h₂ => Subtype.ext (boundary_injective_two (h₁.property.trans h₂.property.symm))⟩

/-- Every `GL₂` hive fibre has at most one element (`hiveCount B ≤ 1`). -/
theorem hiveCount_le_one_two (B : Fin 3 → Fin 2 → ℤ) : hiveCount B ≤ 1 :=
  Fintype.card_le_one_iff_subsingleton.mpr inferInstance

/-- Rank-`2` check `c^{(2, 0)}_{(1, 0), (1, 0)} = 1`. -/
theorem hiveCount_two_std_std_sym :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩) = 1 := by
  have hpos : 0 < hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩) :=
    hiveCount_pos_iff.mpr ⟨⟨exampleTwo, boundary_exampleTwo⟩⟩
  have hle := hiveCount_le_one_two
    (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩)
  omega

/-- Rank-`2` check `c^{(1, 1)}_{(1, 0), (1, 0)} = 1`. -/
theorem hiveCount_two_std_std_det :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩) = 1 := by
  have hpos : 0 < hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩) :=
    hiveCount_pos_iff.mpr ⟨⟨detTwo, boundary_detTwo⟩⟩
  have hle := hiveCount_le_one_two
    (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![1, 1], by decide⟩)
  omega

/-- Rank-`2` exclusion check: `λ = μ = (1, 0)` and `γ = (3, -1)` have equal total degree
`|λ| + |μ| = 2 = |γ|` but violate both `(λ + μ).Dominates γ` (`γ₁ = 3 > 2 = λ₁ + μ₁`) and the
last-coordinate bound `λ₂ + μ₂ ≤ γ₂` (`0 ≤ -1`), so `last_le_of_productBoundary` excludes `γ`. -/
theorem hiveCount_two_std_std_three_neg_one :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![3, -1], by decide⟩) = 0 := by
  rw [hiveCount_eq_zero_iff]
  refine ⟨fun ⟨_, hb⟩ => ?_⟩
  have hlast := last_le_of_productBoundary hb
  simp at hlast

/-- Rank-`2` signed check: `V_{(1, 0)} ⊗ V_{(0, -1)}` contains the trivial module `V_{(0, 0)}` with
multiplicity `1`, reduced by a determinant shift to `c^{(1, 1)}_{(1, 0), (1, 0)} = 1`. -/
theorem hiveCount_two_std_dual_trivial :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, -1], by decide⟩ ⟨![0, 0], by decide⟩) = 1 := by
  rw [← hiveCount_productBoundary_shift _ _ _ 0 1]
  convert hiveCount_two_std_std_det using 2
  ext s i; fin_cases s <;> fin_cases i <;> simp [DominantWeight.dual_apply]

/-- Rank-`2` signed check: `V_{(1, 0)} ⊗ V_{(0, -1)}` contains the adjoint summand `V_{(1, -1)}`
with multiplicity `1`, reduced by a determinant shift to `c^{(2, 0)}_{(1, 0), (1, 0)} = 1`. -/
theorem hiveCount_two_std_dual_adjoint :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, -1], by decide⟩ ⟨![1, -1], by decide⟩) = 1 := by
  rw [← hiveCount_productBoundary_shift _ _ _ 0 1]
  convert hiveCount_two_std_std_sym using 2
  ext s i; fin_cases s <;> fin_cases i <;> simp [DominantWeight.dual_apply]

/-- Rank-`2` signed exclusion check: `γ = (2, -2)` violates `λ₂ + μ₂ ≤ γ₂` (`-1 ≤ -2`). -/
theorem hiveCount_two_std_dual_excluded :
    hiveCount
      (productBoundary ⟨![1, 0], by decide⟩ ⟨![0, -1], by decide⟩ ⟨![2, -2], by decide⟩) = 0 := by
  rw [hiveCount_eq_zero_iff]
  refine ⟨fun ⟨_, hb⟩ => ?_⟩
  have hlast := last_le_of_productBoundary hb; simp at hlast

/-- On `Δ₃`, the boundary determines every vertex except the unique interior vertex `(1, 1, 1)`. -/
private theorem eq_of_boundary_eq_of_interior_eq_three {h₁ h₂ : IntegerHive 3}
    (hb : h₁.boundary = h₂.boundary) (hm : h₁ ⟨1, 1, 1, rfl⟩ = h₂ ⟨1, 1, 1, rfl⟩) : h₁ = h₂ := by
  refine Hive.ext fun p => ?_
  have := p.sum_eq
  rcases (by omega : p.z = 0 ∨ p.x = 0 ∨ p.y = 0 ∨ (p.x = 1 ∧ p.y = 1 ∧ p.z = 1)) with
    hz | hx | hy | ⟨hx, hy, hz⟩
  · have hp : p = Vertex.edgePoint 3 0 ⟨p.y, by omega⟩ := by ext <;> simp [hz]; omega
    rw [hp, apply_edgePoint_zero, apply_edgePoint_zero, hb]
  · have hp : p = Vertex.edgePoint 3 1 ⟨p.z, by omega⟩ := by ext <;> simp [hx]; omega
    rw [hp, apply_edgePoint_one, apply_edgePoint_one, hb]
  · have hp : p = Vertex.edgePoint 3 2 ⟨p.x, by omega⟩ := by ext <;> simp [hy]; omega
    rw [hp, apply_edgePoint_two, apply_edgePoint_two, hb]
  · have hp : p = ⟨1, 1, 1, rfl⟩ := by ext <;> simp [hx, hy, hz]
    rw [hp, hm]

private def hiveThreeTwoOneFun (t : ℤ) (p : Vertex 3) : ℤ :=
  match p.z, p.y + p.z with
  | 0, 1 => 2
  | 0, 2 | 0, 3 | 1, 1 => 3
  | 1, 2 => t
  | 1, 3 | 2, 2 => 5
  | 2, 3 | 3, 3 => 6
  | _, _ => 0

private theorem isRhombusConcave_hiveThreeTwoOneFun {t : ℤ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    IsRhombusConcave (hiveThreeTwoOneFun t) := by
  rw [isRhombusConcave_iff_ofChart]
  refine ⟨fun i j hij hj => ?_, fun i j hij hj => ?_, fun i j hij hj => ?_⟩
  · have : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hiveThreeTwoOneFun] <;> omega
  · have : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hiveThreeTwoOneFun] <;> omega
  · have : (i = 0 ∧ j = 0) ∨ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 1) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hiveThreeTwoOneFun] <;> omega

/-- Parameterized family of size-`3` hives with boundary `((2, 1, 0), (2, 1, 0), (3, 2, 1)*)` and
interior entry `t ∈ {4, 5}` at `(1, 1, 1)`. -/
private def hiveThreeTwoOne (t : ℤ) (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    FixedIntegerHive
      (productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩
        ⟨![3, 2, 1], by decide⟩) :=
  ⟨⟨hiveThreeTwoOneFun t, by simp [hiveThreeTwoOneFun],
      fun hr => (isRhombusConcave_def _).mp (isRhombusConcave_hiveThreeTwoOneFun ht4 ht5) hr⟩,
    by
      ext s i; fin_cases s <;> fin_cases i <;>
        simp [boundary_apply, DominantWeight.dual_apply, hiveThreeTwoOneFun]⟩

private theorem hiveThreeTwoOne_interior (t : ℤ) (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    (hiveThreeTwoOne t ht4 ht5).val ⟨1, 1, 1, rfl⟩ = t := rfl

/-- **First multiplicity-`2` check**: `c^{(3, 2, 1)}_{(2, 1, 0), (2, 1, 0)} = 2`, realized by the
two integer hives with interior values `4` and `5` at `(1, 1, 1)`. -/
theorem hiveCount_three_two_one_two_one_three_two_one :
    hiveCount
      (productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩
        ⟨![3, 2, 1], by decide⟩) = 2 := by
  let B := productBoundary ⟨![2, 1, 0], by decide⟩ ⟨![2, 1, 0], by decide⟩
    ⟨![3, 2, 1], by decide⟩
  have hbound : ∀ h : FixedIntegerHive B,
      h.val ⟨1, 1, 1, rfl⟩ = 4 ∨ h.val ⟨1, 1, 1, rfl⟩ = 5 := fun h => by
    have hu1 := h.val.le_of_isRhombus (isRhombus_ofChart_diag_y (n := 3) (i := 0) (j := 1)
      (by omega) (by omega))
    have hu2 := h.val.le_of_isRhombus (isRhombus_ofChart_diag_y (n := 3) (i := 0) (j := 2)
      (by omega) (by omega))
    have h01 : h.val (Vertex.ofChart 3 0 1 (by omega) (by omega)) = 2 := by
      rw [Vertex.ofChart_zero_left, apply_edgePoint_zero, h.property]
      simp [B, Finset.sum_filter]
    have h02 : h.val (Vertex.ofChart 3 0 2 (by omega) (by omega)) = 3 := by
      rw [Vertex.ofChart_zero_left, apply_edgePoint_zero, h.property]
      simp [B, Finset.sum_filter, Fin.sum_univ_three]
    have h03 : h.val (Vertex.ofChart 3 0 3 (by omega) (by omega)) = 3 := by
      rw [Vertex.ofChart_zero_left, apply_edgePoint_zero, h.property]
      simp [B, Fin.sum_univ_three]
    have h11 : h.val (Vertex.ofChart 3 1 1 (by omega) (by omega)) = 3 := by
      rw [Vertex.ofChart_self, apply_edgePoint_two, h.property]
      simp [B, Finset.sum_filter, Fin.sum_univ_three, DominantWeight.dual_apply]
    have h13 : h.val (Vertex.ofChart 3 1 3 (by omega) (by omega)) = 5 := by
      rw [Vertex.ofChart_right, apply_edgePoint_one, h.property]
      simp [B, Finset.sum_filter, Fin.sum_univ_three]
    have hm : Vertex.ofChart 3 1 2 (by omega) (by omega) = ⟨1, 1, 1, rfl⟩ := by ext <;> simp
    rw [h01, h02, h11, hm] at hu1; rw [h02, h03, h13, hm] at hu2
    omega
  let e : FixedIntegerHive B ≃ Bool :=
    { toFun := fun h => decide (h.val ⟨1, 1, 1, rfl⟩ = 4)
      invFun := fun b => if b then hiveThreeTwoOne 4 le_rfl (by omega)
        else hiveThreeTwoOne 5 (by omega) le_rfl
      left_inv := fun h => Subtype.ext <| by
        rcases hbound h with h4 | h5
        · simp only [h4, decide_true, ↓reduceIte]
          exact eq_of_boundary_eq_of_interior_eq_three
            ((hiveThreeTwoOne 4 le_rfl (by omega)).property.trans h.property.symm)
            (by rw [hiveThreeTwoOne_interior, h4])
        · have h54 : (5 : ℤ) ≠ 4 := by omega
          simp only [h5, h54, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact eq_of_boundary_eq_of_interior_eq_three
            ((hiveThreeTwoOne 5 (by omega) le_rfl).property.trans h.property.symm)
            (by rw [hiveThreeTwoOne_interior, h5])
      right_inv := fun b => by cases b <;> simp [hiveThreeTwoOne_interior] }
  rw [← card_fixedIntegerHive, Fintype.card_congr e, Fintype.card_bool]

end RankChecks

end TauCeti.Hive
