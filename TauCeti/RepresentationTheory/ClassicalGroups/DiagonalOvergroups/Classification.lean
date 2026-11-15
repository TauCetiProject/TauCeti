/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import TauCeti.Algebra.Lie.GeneralLinear.Radical
public import TauCeti.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.RepresentationTheory.ClassicalGroups.DiagonalOvergroups.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Units
import TauCeti.Analysis.Matrix.GeneralLinearGroup.Connected
import TauCeti.Analysis.Matrix.SpecialLinearGroup.Connected
import TauCeti.Geometry.Lie.Exponential.Matrix.SpecialLinear
import TauCeti.Geometry.Lie.Subgroup.CartanChart
import TauCeti.Geometry.Lie.Subgroup.Center
import TauCeti.Geometry.Lie.Subgroup.Units
import TauCeti.Topology.Algebra.Group.Goursat
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Classification of connected complex diagonal overgroups of `GL ι ℂ`

Every closed, connected subgroup `H ≤ GL ι ℂ × GL ι ℂ` containing the diagonal `Δ` whose
exponential tangent directions are closed under complex scalar multiplication equals one of four
subgroups:

* `diagonal ι ℂ` (`{(g, g)}`),
* `scalarDiagonal ι ℂ` (`{(scalar ι u * g, g)}`),
* `determinantEqual ι ℂ` (`{(g, h) | det g = det h}`),
* `⊤` (`GL ι ℂ × GL ι ℂ`).

## Proof architecture

1. **Lie subalgebra classification**
   (`eq_diagonalLie_or_eq_scalarDiagonalLie_or_eq_traceEqualLie_or_eq_top`).
   Over any field `K` of characteristic not `2`, let `L` be a `K`-Lie subalgebra of
   `Matrix ι ι K × Matrix ι ι K` containing the diagonal `{(A, A)}`. Its first-factor slice
   `{Z | (Z, 0) ∈ L}` is stable under `⁅A, Z⁆` because `⁅(A, A), (Z, 0)⁆ = (⁅A, Z⁆, 0)`, so it is a
   `LieIdeal K (Matrix ι ι K)`. Since `(X, Y) ∈ L ↔ X - Y ∈ {Z | (Z, 0) ∈ L}`, applying the
   four-case Lie-ideal theorem `TauCeti.eq_bot_or_eq_center_or_eq_slIdeal_or_eq_top` classifies `L`
   into `diagonalLie K ι`, `scalarDiagonalLie K ι`, `traceEqualLie K ι`, or `⊤`, uniformly across
   all finite index types `ι`.
2. **Closedness and connectedness.** Using the Goursat normal-kernel homeomorphism
   `Subgroup.goursatCoordHomeomorph` together with connectedness of `GL ι ℂ`, `SL ι ℂ`, and `ℂˣ`,
   all four complex subgroups are closed and path-connected.
3. **Exponential tangent comparison (`connected_complex_overgroup`).** Pulling `H` back along
   `ContinuousMulEquiv.prodUnits` identifies `realDirections H` with
   `TauCeti.Lie.lieSubalgebraOfSubgroup` in `(Matrix ι ι ℂ × Matrix ι ι ℂ)ˣ`. Complex closure turns
   `realDirections H` into a complex Lie subalgebra containing `diagonalLie ℂ ι`; matching it with
   the exponential tangent spaces of the four model subgroups and applying
   `TauCeti.Lie.le_of_lieSubalgebraOfSubgroup_le` in both directions recovers `H`.

Rank-specific collapse and strictness (`|ι| = 0`, `|ι| = 1`, `|ι| ≥ 2`) together with the real
counterexample `|det g / det h| = 1` are developed in
`TauCeti.RepresentationTheory.ClassicalGroups.DiagonalOvergroups.RankComparison`.

## Main definitions

* `TauCeti.DiagonalOvergroups.diagonalLie`, `scalarDiagonalLie`, `traceEqualLie`: the intermediate
  Lie subalgebras of `Matrix ι ι R × Matrix ι ι R`.
* `TauCeti.DiagonalOvergroups.pairExp`: componentwise matrix exponential into `GL ι ℂ × GL ι ℂ`.
* `TauCeti.DiagonalOvergroups.realDirections`: matrix pairs whose real one-parameter subgroup lies
  in `H`.

## Main results

* `TauCeti.DiagonalOvergroups.eq_diagonalLie_or_eq_scalarDiagonalLie_or_eq_traceEqualLie_or_eq_top`:
  classification of `K`-Lie subalgebras of `Matrix ι ι K × Matrix ι ι K` containing the diagonal
  when `(2 : K) ≠ 0`.
* `TauCeti.DiagonalOvergroups.forall_pairExp_complex_smul_mem_iff_smul_I_mem`: complex closure of
  `realDirections H` is equivalent to stability under `Complex.I • ·`.
* `TauCeti.DiagonalOvergroups.connected_complex_overgroup`: classification of closed connected
  complex diagonal overgroups of `GL ι ℂ`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Springer GTM 222,
  2015, Chapters 2–3.
* James E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Springer GTM 9,
  1972, Chapter I.
-/

public section

open Matrix NormedSpace

namespace TauCeti.DiagonalOvergroups

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Lie subalgebras containing the diagonal -/

section LieClassification

variable (R ι : Type*) [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The diagonal Lie subalgebra `{(X, X)}` of `Matrix ι ι R × Matrix ι ι R`. -/
def diagonalLie : LieSubalgebra R (Matrix ι ι R × Matrix ι ι R) where
  carrier := {X | X.1 = X.2}
  add_mem' {X Y} hX hY := by
    change (X + Y).1 = (X + Y).2
    rw [Prod.fst_add, Prod.snd_add, hX, hY]
  zero_mem' := rfl
  smul_mem' c {X} hX := by
    change (c • X).1 = (c • X).2
    rw [Prod.smul_fst, Prod.smul_snd, hX]
  lie_mem' {X Y} hX hY := by
    change ⁅X.1, Y.1⁆ = ⁅X.2, Y.2⁆
    rw [hX, hY]

/-- The scalar-diagonal Lie subalgebra `{(c • 1 + Y, Y)}` of `Matrix ι ι R × Matrix ι ι R`. -/
def scalarDiagonalLie : LieSubalgebra R (Matrix ι ι R × Matrix ι ι R) where
  carrier := {X | ∃ c : R, X.1 = c • 1 + X.2}
  add_mem' := by
    rintro X Y ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
    exact ⟨c₁ + c₂, by rw [Prod.fst_add, Prod.snd_add, hc₁, hc₂, add_smul]; abel⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' r := by
    rintro X ⟨c, hc⟩
    exact ⟨r * c, by rw [Prod.smul_fst, Prod.smul_snd, hc, smul_add, mul_smul]⟩
  lie_mem' := by
    rintro X Y ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
    refine ⟨0, ?_⟩
    change ⁅X.1, Y.1⁆ = (0 : R) • 1 + ⁅X.2, Y.2⁆
    rw [zero_smul, zero_add, hc₁, hc₂]
    have h1 : c₁ • (c₂ • (1 : Matrix ι ι R)) = c₂ • (c₁ • 1) := by
      rw [smul_smul, smul_smul, mul_comm]
    simp only [LieRing.of_associative_ring_bracket, add_mul, mul_add, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one, smul_add, h1]
    abel

/-- The trace-equal Lie subalgebra `{(X, Y) | X.trace = Y.trace}` of
`Matrix ι ι R × Matrix ι ι R`. -/
def traceEqualLie : LieSubalgebra R (Matrix ι ι R × Matrix ι ι R) where
  carrier := {X | X.1.trace = X.2.trace}
  add_mem' {X Y} hX hY := by
    change (X.1 + Y.1).trace = (X.2 + Y.2).trace
    rw [Matrix.trace_add, Matrix.trace_add, hX, hY]
  zero_mem' := by simp
  smul_mem' c {X} hX := by
    change (c • X.1).trace = (c • X.2).trace
    rw [Matrix.trace_smul, Matrix.trace_smul, hX]
  lie_mem' {X Y} _ _ := by
    change (X.1 * Y.1 - Y.1 * X.1).trace = (X.2 * Y.2 - Y.2 * X.2).trace
    rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_mul_comm X.1 Y.1,
      Matrix.trace_mul_comm X.2 Y.2, sub_self, sub_self]

variable {R ι}

@[simp]
theorem mem_diagonalLie_iff {X : Matrix ι ι R × Matrix ι ι R} :
    X ∈ diagonalLie R ι ↔ X.1 = X.2 :=
  Iff.rfl

@[simp]
theorem mem_scalarDiagonalLie_iff {X : Matrix ι ι R × Matrix ι ι R} :
    X ∈ scalarDiagonalLie R ι ↔ ∃ c : R, X.1 = c • 1 + X.2 :=
  Iff.rfl

@[simp]
theorem mem_traceEqualLie_iff {X : Matrix ι ι R × Matrix ι ι R} :
    X ∈ traceEqualLie R ι ↔ X.1.trace = X.2.trace :=
  Iff.rfl

/-- **Lie-algebra overgroup classification**: over a field `K` of characteristic not `2`, every
`K`-Lie subalgebra of `Matrix ι ι K × Matrix ι ι K` containing `diagonalLie K ι` is one of
`diagonalLie K ι`, `scalarDiagonalLie K ι`, `traceEqualLie K ι`, or `⊤`. -/
theorem eq_diagonalLie_or_eq_scalarDiagonalLie_or_eq_traceEqualLie_or_eq_top
    {K : Type*} [Field K] (htwo : (2 : K) ≠ 0)
    (L : LieSubalgebra K (Matrix ι ι K × Matrix ι ι K)) (hd : diagonalLie K ι ≤ L) :
    L = diagonalLie K ι ∨ L = scalarDiagonalLie K ι ∨ L = traceEqualLie K ι ∨ L = ⊤ := by
  let fstIdeal : LieIdeal K (Matrix ι ι K) :=
    { carrier := {Z | (Z, 0) ∈ L}
      add_mem' {A B} hA hB := by simpa using L.add_mem hA hB
      zero_mem' := L.zero_mem
      smul_mem' c {Z} hZ := by simpa using L.smul_mem c hZ
      lie_mem {A Z} hZ := by
        have hA : (A, A) ∈ L := hd rfl
        simpa using L.lie_mem hA hZ }
  have hmem : ∀ X : Matrix ι ι K × Matrix ι ι K, X ∈ L ↔ X.1 - X.2 ∈ fstIdeal := by
    rintro ⟨X₁, X₂⟩
    have hdiag : (X₂, X₂) ∈ L := hd rfl
    refine ⟨fun hX => ?_, fun hsub => ?_⟩
    · simpa [fstIdeal] using L.sub_mem hX hdiag
    · simpa using L.add_mem hsub hdiag
  rcases TauCeti.eq_bot_or_eq_center_or_eq_slIdeal_or_eq_top fstIdeal htwo with hI | hI | hI | hI
  · left
    ext X
    rw [hmem, hI, LieSubmodule.mem_bot, sub_eq_zero, mem_diagonalLie_iff]
  · right; left
    ext X
    rw [hmem, hI, TauCeti.mem_center_matrix_iff, mem_scalarDiagonalLie_iff]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, eq_add_of_sub_eq hc⟩, fun ⟨c, hc⟩ => ⟨c, sub_eq_of_eq_add hc⟩⟩
  · right; right; left
    ext X
    rw [hmem, hI, TauCeti.mem_slIdeal_iff, Matrix.trace_sub, sub_eq_zero, mem_traceEqualLie_iff]
  · right; right; right
    ext X
    simp [hmem, hI]

end LieClassification

/-! ### Closedness and path-connectedness of the four model subgroups -/

section ModelTopology

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
theorem isClosed_diagonal [T2Space R] : IsClosed (diagonal ι R : Set (GL ι R × GL ι R)) := by
  have hset : (diagonal ι R : Set (GL ι R × GL ι R)) = {p | p.1 = p.2} :=
    Set.ext fun _ => mem_diagonal_iff
  rw [hset]
  exact isClosed_eq continuous_fst continuous_snd

theorem isClosed_scalarDiagonal [T2Space R] :
    IsClosed (scalarDiagonal ι R : Set (GL ι R × GL ι R)) := by
  have hd : (MonoidHom.id (GL ι R)).graph ≤ scalarDiagonal ι R :=
    diagonal_eq_graph_id (ι := ι) (R := R) ▸ diagonal_le_scalarDiagonal
  rw [Subgroup.isClosed_iff_isClosed_goursatFst hd, goursatFst_scalarDiagonal]
  exact Subgroup.isClosed_center

theorem isClosed_determinantEqual [T2Space R] :
    IsClosed (determinantEqual ι R : Set (GL ι R × GL ι R)) := by
  have hd : (MonoidHom.id (GL ι R)).graph ≤ determinantEqual ι R :=
    diagonal_eq_graph_id (ι := ι) (R := R) ▸ diagonal_le_determinantEqual
  rw [Subgroup.isClosed_iff_isClosed_goursatFst hd, goursatFst_determinantEqual]
  exact MonoidHom.coe_range (SpecialLinearGroup.toGL (n := ι) (R := R)) ▸
    SpecialLinearGroup.isClosedEmbedding_toGL.isClosed_range

instance instPathConnectedSpaceDiagonal : PathConnectedSpace (diagonal ι ℂ) := by
  have hd : (MonoidHom.id (GL ι ℂ)).graph ≤ diagonal ι ℂ :=
    (diagonal_eq_graph_id (ι := ι) (R := ℂ)).ge
  rw [Subgroup.pathConnectedSpace_iff_pathConnectedSpace_goursatFst hd, goursatFst_diagonal]
  exact ⟨⟨1⟩, fun x y => Subsingleton.elim x y ▸ Joined.refl x⟩

instance instPathConnectedSpaceScalarDiagonal : PathConnectedSpace (scalarDiagonal ι ℂ) := by
  have hsc : Continuous (GeneralLinearGroup.scalar ι : ℂˣ → GL ι ℂ) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · simpa only [Function.comp_def, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using
        (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
    · simpa only [Function.comp_def, MulOpposite.op_inv, ← map_inv,
        GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using
        (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal
  have hcont_map : Continuous (scalarDiagonalMap ι ℂ) := by
    have heq : ⇑(scalarDiagonalMap ι ℂ) =
        fun p : GL ι ℂ × ℂˣ => (GeneralLinearGroup.scalar ι p.2 * p.1, p.1) :=
      funext (scalarDiagonalMap_apply (ι := ι) (R := ℂ))
    rw [heq]
    exact ((hsc.comp continuous_snd).mul continuous_fst).prodMk continuous_fst
  let f : GL ι ℂ × ℂˣ → scalarDiagonal ι ℂ := fun p =>
    ⟨scalarDiagonalMap ι ℂ p, mem_scalarDiagonal_iff.mpr ⟨p.2, by simp⟩⟩
  have hf : Function.Surjective f := fun ⟨q, hq⟩ => by
    obtain ⟨u, hu⟩ := mem_scalarDiagonal_iff.mp hq
    exact ⟨(q.2, u), Subtype.ext (Prod.ext (by simp [f, hu]) (by simp [f]))⟩
  exact hf.pathConnectedSpace (hcont_map.subtype_mk _)

instance instPathConnectedSpaceDeterminantEqual : PathConnectedSpace (determinantEqual ι ℂ) := by
  have hd : (MonoidHom.id (GL ι ℂ)).graph ≤ determinantEqual ι ℂ :=
    diagonal_eq_graph_id (ι := ι) (R := ℂ) ▸ diagonal_le_determinantEqual
  rw [Subgroup.pathConnectedSpace_iff_pathConnectedSpace_goursatFst hd, goursatFst_determinantEqual]
  exact (SpecialLinearGroup.toGL (n := ι) (R := ℂ)).rangeRestrict_surjective.pathConnectedSpace
    (SpecialLinearGroup.isClosedEmbedding_toGL.continuous.subtype_mk _)

end ModelTopology

/-! ### Componentwise matrix exponential and exponential tangent directions -/

section Exponential

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Componentwise matrix exponential** `Matrix ι ι ℂ × Matrix ι ι ℂ → GL ι ℂ × GL ι ℂ`. -/
noncomputable def pairExp (X : Matrix ι ι ℂ × Matrix ι ι ℂ) : GL ι ℂ × GL ι ℂ :=
  ((Matrix.isUnit_exp X.1).unit, (Matrix.isUnit_exp X.2).unit)

@[simp]
theorem coe_fst_pairExp (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    ((pairExp X).1 : Matrix ι ι ℂ) = NormedSpace.exp X.1 :=
  (Matrix.isUnit_exp X.1).unit_spec

@[simp]
theorem coe_snd_pairExp (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    ((pairExp X).2 : Matrix ι ι ℂ) = NormedSpace.exp X.2 :=
  (Matrix.isUnit_exp X.2).unit_spec

@[simp]
theorem pairExp_zero : pairExp (0 : Matrix ι ι ℂ × Matrix ι ι ℂ) = 1 :=
  Prod.ext (Units.ext (by simp)) (Units.ext (by simp))

theorem pairExp_add_of_commute {X Y : Matrix ι ι ℂ × Matrix ι ι ℂ} (h : Commute X Y) :
    pairExp (X + Y) = pairExp X * pairExp Y := by
  have h1 : Commute X.1 Y.1 := congrArg Prod.fst h
  have h2 : Commute X.2 Y.2 := congrArg Prod.snd h
  exact Prod.ext
    (Units.ext (by simp [Matrix.exp_add_of_commute X.1 Y.1 h1]))
    (Units.ext (by simp [Matrix.exp_add_of_commute X.2 Y.2 h2]))

@[simp]
theorem pairExp_add_smul (z w : ℂ) (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    pairExp ((z + w) • X) = pairExp (z • X) * pairExp (w • X) := by
  rw [add_smul]
  exact pairExp_add_of_commute (((Commute.refl X).smul_left z).smul_right w)

@[simp]
theorem pairExp_add_real_smul (s t : ℝ) (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    pairExp ((s + t) • X) = pairExp (s • X) * pairExp (t • X) := by
  rw [← algebraMap_smul ℂ (s + t) X, map_add, pairExp_add_smul, algebraMap_smul, algebraMap_smul]

@[simp]
theorem pairExp_neg (X : Matrix ι ι ℂ × Matrix ι ι ℂ) : pairExp (-X) = (pairExp X)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pairExp_add_of_commute (Commute.refl X).neg_left, neg_add_cancel, pairExp_zero]

/-- **Real exponential directions** of a subgroup `H ≤ GL ι ℂ × GL ι ℂ`: the matrix pairs whose
entire real one-parameter subgroup lies in `H`. -/
def realDirections (H : Subgroup (GL ι ℂ × GL ι ℂ)) :
    Set (Matrix ι ι ℂ × Matrix ι ι ℂ) :=
  {X | ∀ t : ℝ, pairExp (t • X) ∈ H}

@[simp]
theorem mem_realDirections_iff {H : Subgroup (GL ι ℂ × GL ι ℂ)}
    {X : Matrix ι ι ℂ × Matrix ι ι ℂ} :
    X ∈ realDirections H ↔ ∀ t : ℝ, pairExp (t • X) ∈ H :=
  Iff.rfl

theorem realDirections_mono {H₁ H₂ : Subgroup (GL ι ℂ × GL ι ℂ)} (h : H₁ ≤ H₂) :
    realDirections H₁ ≤ realDirections H₂ :=
  fun _ hX t => h (hX t)

@[simp]
theorem realDirections_top :
    realDirections (⊤ : Subgroup (GL ι ℂ × GL ι ℂ)) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ => Subgroup.mem_top _

/-- **Complex closure of `realDirections H` is equivalent to `Complex.I`-invariance**, for every
subgroup `H ≤ GL ι ℂ × GL ι ℂ`. -/
theorem forall_pairExp_complex_smul_mem_iff_smul_I_mem (H : Subgroup (GL ι ℂ × GL ι ℂ)) :
    (∀ X ∈ realDirections H, ∀ z : ℂ, pairExp (z • X) ∈ H) ↔
      ∀ X ∈ realDirections H, Complex.I • X ∈ realDirections H := by
  constructor
  · intro h X hX t
    have hsmul : (t : ℝ) • (Complex.I • X) = ((t : ℂ) * Complex.I) • X := by
      rw [← algebraMap_smul ℂ t (Complex.I • X), smul_smul, Complex.coe_algebraMap]
    rw [hsmul]
    exact h X hX _
  · intro hI X hX z
    have hz : z • X = z.re • X + z.im • (Complex.I • X) := by
      rw [← algebraMap_smul ℂ z.re X, ← algebraMap_smul ℂ z.im (Complex.I • X), smul_smul,
        Complex.coe_algebraMap, ← add_smul, Complex.re_add_im]
    have hcomm : Commute (z.re • X) (z.im • (Complex.I • X)) := by
      rw [← algebraMap_smul ℂ z.re X, ← algebraMap_smul ℂ z.im (Complex.I • X), smul_smul]
      exact ((Commute.refl X).smul_left _).smul_right _
    rw [hz, pairExp_add_of_commute hcomm]
    exact H.mul_mem (hX z.re) (hI X hX z.im)

/-! ### Closed-subgroup Lie algebra bridge and main classification theorem -/

private theorem isPreconnected_diagonal :
    IsPreconnected (diagonal ι ℂ : Set (GL ι ℂ × GL ι ℂ)) :=
  isPreconnected_iff_preconnectedSpace.mpr (inferInstanceAs (PreconnectedSpace (diagonal ι ℂ)))

private theorem isPreconnected_scalarDiagonal :
    IsPreconnected (scalarDiagonal ι ℂ : Set (GL ι ℂ × GL ι ℂ)) :=
  isPreconnected_iff_preconnectedSpace.mpr
    (inferInstanceAs (PreconnectedSpace (scalarDiagonal ι ℂ)))

private theorem isPreconnected_determinantEqual :
    IsPreconnected (determinantEqual ι ℂ : Set (GL ι ℂ × GL ι ℂ)) :=
  isPreconnected_iff_preconnectedSpace.mpr
    (inferInstanceAs (PreconnectedSpace (determinantEqual ι ℂ)))

private theorem isPreconnected_univ_pair :
    IsPreconnected (Set.univ : Set (GL ι ℂ × GL ι ℂ)) := by
  have : PathConnectedSpace (GL ι ℂ) := TauCeti.instPathConnectedSpaceMatrixGeneralLinearGroup
  exact isPreconnected_univ

section LieBridge

open Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] TauCeti.normedAlgebraRatOfReal

private theorem prodUnits_expUnit_eq_pairExp (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    ContinuousMulEquiv.prodUnits (Matrix ι ι ℂ) (Matrix ι ι ℂ) (TauCeti.expUnit X) =
      pairExp X := by
  rw [← ContinuousMulEquiv.eq_symm_apply]
  refine Units.ext (Prod.ext ?_ ?_)
  · change (TauCeti.expUnit X : Matrix ι ι ℂ × Matrix ι ι ℂ).1 = ((pairExp X).1 : Matrix ι ι ℂ)
    rw [TauCeti.expUnit_coe, Prod.fst_exp, coe_fst_pairExp]
    rfl
  · change (TauCeti.expUnit X : Matrix ι ι ℂ × Matrix ι ι ℂ).2 = ((pairExp X).2 : Matrix ι ι ℂ)
    rw [TauCeti.expUnit_coe, Prod.snd_exp, coe_snd_pairExp]
    rfl

private theorem mem_realDirections_iff_mem_lieSubalgebraOfSubgroup
    {H : Subgroup (GL ι ℂ × GL ι ℂ)} (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ)))
    (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    X ∈ realDirections H ↔
      (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix ι ι ℂ × Matrix ι ι ℂ)).symm X ∈
        TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix ι ι ℂ × Matrix ι ι ℂ))
          (H.comap (ContinuousMulEquiv.prodUnits (Matrix ι ι ℂ) (Matrix ι ι ℂ)).toMonoidHom) := by
  have hc' : IsClosed ((H.comap
      (ContinuousMulEquiv.prodUnits (Matrix ι ι ℂ) (Matrix ι ι ℂ)).toMonoidHom :
        Subgroup (Matrix ι ι ℂ × Matrix ι ι ℂ)ˣ) : Set (Matrix ι ι ℂ × Matrix ι ι ℂ)ˣ) :=
    hc.preimage (map_continuous (ContinuousMulEquiv.prodUnits (Matrix ι ι ℂ) (Matrix ι ι ℂ)))
  rw [TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff hc']
  exact forall_congr' fun t => by
    rw [Subgroup.mem_comap]
    change pairExp (t • X) ∈ H ↔
      ContinuousMulEquiv.prodUnits (Matrix ι ι ℂ) (Matrix ι ι ℂ) (TauCeti.expUnit (t • X)) ∈ H
    rw [prodUnits_expUnit_eq_pairExp]

/-- **Real tangent Lie subalgebra** of a closed subgroup `H ≤ GL ι ℂ × GL ι ℂ`, with underlying
carrier `realDirections H`. -/
noncomputable def realTangentLieSubalgebra (H : Subgroup (GL ι ℂ × GL ι ℂ))
    (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ))) :
    LieSubalgebra ℝ (Matrix ι ι ℂ × Matrix ι ι ℂ) where
  carrier := realDirections H
  add_mem' {X Y} hX hY := by
    change X + Y ∈ realDirections H
    rw [mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc, map_add]
    exact LieSubalgebra.add_mem _
      ((mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc X).mp hX)
      ((mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc Y).mp hY)
  zero_mem' := by simp [realDirections]
  smul_mem' r {X} hX := fun t => by
    rw [smul_smul]
    exact hX (t * r)
  lie_mem' {X Y} hX hY := by
    rw [mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc,
      (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix ι ι ℂ × Matrix ι ι ℂ)).symm.map_lie]
    exact LieSubalgebra.lie_mem _
      ((mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc X).mp hX)
      ((mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc Y).mp hY)

@[simp]
theorem mem_realTangentLieSubalgebra_iff {H : Subgroup (GL ι ℂ × GL ι ℂ)}
    (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ))) {X : Matrix ι ι ℂ × Matrix ι ι ℂ} :
    X ∈ realTangentLieSubalgebra H hc ↔ X ∈ realDirections H :=
  Iff.rfl

/-- **Complex tangent Lie subalgebra** of a closed complex-closed subgroup `H ≤ GL ι ℂ × GL ι ℂ`. -/
noncomputable def complexTangentLieSubalgebra (H : Subgroup (GL ι ℂ × GL ι ℂ))
    (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ)))
    (hcomplex : ∀ X ∈ realDirections H, ∀ z : ℂ, pairExp (z • X) ∈ H) :
    LieSubalgebra ℂ (Matrix ι ι ℂ × Matrix ι ι ℂ) where
  carrier := realDirections H
  add_mem' {X Y} hX hY := (realTangentLieSubalgebra H hc).add_mem hX hY
  zero_mem' := (realTangentLieSubalgebra H hc).zero_mem
  smul_mem' z {X} hX t := by
    have hsmul : (t : ℝ) • (z • X) = ((t : ℂ) * z) • X := by
      rw [← algebraMap_smul ℂ t (z • X), smul_smul, Complex.coe_algebraMap]
    rw [hsmul]
    exact hcomplex X hX _
  lie_mem' {X Y} hX hY := (realTangentLieSubalgebra H hc).lie_mem hX hY

@[simp]
theorem mem_complexTangentLieSubalgebra_iff {H : Subgroup (GL ι ℂ × GL ι ℂ)}
    (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ)))
    (hcomplex : ∀ X ∈ realDirections H, ∀ z : ℂ, pairExp (z • X) ∈ H)
    {X : Matrix ι ι ℂ × Matrix ι ι ℂ} :
    X ∈ complexTangentLieSubalgebra H hc hcomplex ↔ X ∈ realDirections H :=
  Iff.rfl

/-- Inclusion of closed subgroups of `GL ι ℂ × GL ι ℂ` from inclusion of their `realDirections`
when the smaller subgroup is preconnected. -/
theorem le_of_realDirections_le {H₁ H₂ : Subgroup (GL ι ℂ × GL ι ℂ)}
    (hc₁ : IsClosed (H₁ : Set (GL ι ℂ × GL ι ℂ)))
    (hconn₁ : IsPreconnected (H₁ : Set (GL ι ℂ × GL ι ℂ)))
    (hc₂ : IsClosed (H₂ : Set (GL ι ℂ × GL ι ℂ)))
    (hle : realDirections H₁ ≤ realDirections H₂) :
    H₁ ≤ H₂ := by
  let e := ContinuousMulEquiv.prodUnits (Matrix ι ι ℂ) (Matrix ι ι ℂ)
  let K₁ := H₁.comap e.toMonoidHom
  let K₂ := H₂.comap e.toMonoidHom
  have hK₁ : IsClosed (K₁ : Set (Matrix ι ι ℂ × Matrix ι ι ℂ)ˣ) :=
    hc₁.preimage (map_continuous e)
  have hK₂ : IsClosed (K₂ : Set (Matrix ι ι ℂ × Matrix ι ι ℂ)ˣ) :=
    hc₂.preimage (map_continuous e)
  have hconnK₁ : IsPreconnected (K₁ : Set (Matrix ι ι ℂ × Matrix ι ι ℂ)ˣ) := by
    have himg : e.symm '' (H₁ : Set (GL ι ℂ × GL ι ℂ)) = K₁ := by
      ext u
      constructor
      · rintro ⟨p, hp, rfl⟩
        change e (e.symm p) ∈ H₁
        rwa [e.apply_symm_apply]
      · intro hu
        exact ⟨e u, hu, e.symm_apply_apply u⟩
    rw [← himg]
    exact hconn₁.image _ e.symm.continuous.continuousOn
  have hlie : TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix ι ι ℂ × Matrix ι ι ℂ)) K₁ ≤
      TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix ι ι ℂ × Matrix ι ι ℂ)) K₂ := by
    intro D hD
    let X := TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix ι ι ℂ × Matrix ι ι ℂ) D
    have hDX : (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix ι ι ℂ × Matrix ι ι ℂ)).symm X =
        D := LieEquiv.symm_apply_apply _ D
    rw [← hDX] at hD ⊢
    exact (mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc₂ X).mp
      (hle ((mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc₁ X).mpr hD))
  have hKle : K₁ ≤ K₂ := TauCeti.Lie.le_of_lieSubalgebraOfSubgroup_le hK₁ hconnK₁ hK₂ hlie
  intro p hp
  have hp' : e.symm p ∈ K₁ := by
    change e (e.symm p) ∈ H₁
    rwa [e.apply_symm_apply]
  have hp'' : e (e.symm p) ∈ H₂ := hKle hp'
  rwa [e.apply_symm_apply] at hp''

theorem eq_of_realDirections_eq {H₁ H₂ : Subgroup (GL ι ℂ × GL ι ℂ)}
    (hc₁ : IsClosed (H₁ : Set (GL ι ℂ × GL ι ℂ)))
    (hconn₁ : IsPreconnected (H₁ : Set (GL ι ℂ × GL ι ℂ)))
    (hc₂ : IsClosed (H₂ : Set (GL ι ℂ × GL ι ℂ)))
    (hconn₂ : IsPreconnected (H₂ : Set (GL ι ℂ × GL ι ℂ)))
    (heq : realDirections H₁ = realDirections H₂) :
    H₁ = H₂ :=
  le_antisymm
    (le_of_realDirections_le hc₁ hconn₁ hc₂ heq.le)
    (le_of_realDirections_le hc₂ hconn₂ hc₁ heq.ge)

@[simp]
theorem realDirections_diagonal :
    realDirections (diagonal ι ℂ) = (diagonalLie ℂ ι : Set (Matrix ι ι ℂ × Matrix ι ι ℂ)) := by
  ext X
  simp only [mem_realDirections_iff, mem_diagonal_iff, Units.ext_iff, coe_fst_pairExp,
    coe_snd_pairExp, Prod.smul_fst, Prod.smul_snd, SetLike.mem_coe, mem_diagonalLie_iff]
  exact ⟨TauCeti.eq_of_forall_exp_smul_eq, fun h t => by rw [h]⟩

private theorem mem_center_of_pairExp_sub_mem_scalarDiagonal {Z : Matrix ι ι ℂ}
    (hsub : (Z, 0) ∈ realDirections (scalarDiagonal ι ℂ)) :
    Z ∈ LieAlgebra.center ℂ (Matrix ι ι ℂ) := by
  have hcenter : ∀ t : ℝ, TauCeti.expUnit (t • Z) ∈ Subgroup.center (Matrix ι ι ℂ)ˣ := by
    intro t
    obtain ⟨u, hu⟩ := mem_scalarDiagonal_iff.mp (hsub t)
    have hu2 : (pairExp (t • (Z, (0 : Matrix ι ι ℂ)))).2 = 1 := Units.ext (by simp)
    rw [hu2, mul_one] at hu
    have heq : TauCeti.expUnit (t • Z) = GeneralLinearGroup.scalar ι u := Units.ext <| by
      rw [TauCeti.expUnit_coe]
      exact (coe_fst_pairExp (t • (Z, (0 : Matrix ι ι ℂ)))).symm.trans (congrArg Units.val hu)
    rw [heq, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u, rfl⟩
  have hlie := (TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff
    Subgroup.isClosed_center Z).mpr hcenter
  have hzc := TauCeti.Lie.lieSubalgebraOfSubgroup_center_le hlie
  rw [LieAlgebra.center, LieModule.mem_maxTrivSubmodule]
  intro B
  let e := TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix ι ι ℂ)
  have h0 : ⁅e.symm B, e.symm Z⁆ = 0 :=
    (LieModule.mem_maxTrivSubmodule ℝ _ _ _).mp hzc (e.symm B)
  have h1 := congrArg e h0
  rw [e.map_lie, e.apply_symm_apply, e.apply_symm_apply, map_zero] at h1
  exact h1

@[simp]
theorem realDirections_scalarDiagonal :
    realDirections (scalarDiagonal ι ℂ) =
      (scalarDiagonalLie ℂ ι : Set (Matrix ι ι ℂ × Matrix ι ι ℂ)) := by
  ext X
  simp only [SetLike.mem_coe, mem_scalarDiagonalLie_iff]
  constructor
  · intro hX
    have hdiag : (X.2, X.2) ∈ realTangentLieSubalgebra (scalarDiagonal ι ℂ)
        isClosed_scalarDiagonal :=
      realDirections_mono diagonal_le_scalarDiagonal (by simp [realDirections_diagonal])
    have hsub' : X - (X.2, X.2) ∈ realDirections (scalarDiagonal ι ℂ) :=
      (realTangentLieSubalgebra (scalarDiagonal ι ℂ) isClosed_scalarDiagonal).sub_mem hX hdiag
    have hsub : (X.1 - X.2, 0) ∈ realDirections (scalarDiagonal ι ℂ) :=
      (Prod.ext rfl (sub_self X.2) : X - (X.2, X.2) = (X.1 - X.2, 0)) ▸ hsub'
    obtain ⟨c, hc⟩ := TauCeti.mem_center_matrix_iff.mp
      (mem_center_of_pairExp_sub_mem_scalarDiagonal hsub)
    exact ⟨c, eq_add_of_sub_eq hc⟩
  · rintro ⟨c, hc⟩ t
    rw [mem_scalarDiagonal_iff]
    let u : ℂˣ := (NormedSpace.isUnit_exp (t • c)).unit
    refine ⟨u, Units.ext ?_⟩
    have hsmul : t • X.1 = (t • c) • (1 : Matrix ι ι ℂ) + t • X.2 := by
      rw [hc, smul_add, ← algebraMap_smul ℂ t (c • 1), smul_smul, ← Algebra.smul_def]
    have hcomm : Commute ((t • c) • (1 : Matrix ι ι ℂ)) (t • X.2) :=
      (Commute.one_left (t • X.2)).smul_left (t • c)
    simp only [Prod.smul_fst, Prod.smul_snd, coe_fst_pairExp, coe_snd_pairExp, Units.val_mul]
    rw [hsmul, Matrix.exp_add_of_commute _ _ hcomm, Matrix.smul_one_eq_diagonal,
      Matrix.exp_diagonal, Pi.exp_def, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    exact congrArg (· * _)
      (congrArg Matrix.diagonal (funext fun _ => (NormedSpace.isUnit_exp (t • c)).unit_spec.symm))

@[simp]
theorem realDirections_determinantEqual :
    realDirections (determinantEqual ι ℂ) =
      (traceEqualLie ℂ ι : Set (Matrix ι ι ℂ × Matrix ι ι ℂ)) := by
  ext X
  simp only [SetLike.mem_coe, mem_traceEqualLie_iff]
  constructor
  · intro hX
    have hdiag : (X.2, X.2) ∈ realTangentLieSubalgebra (determinantEqual ι ℂ)
        isClosed_determinantEqual :=
      realDirections_mono diagonal_le_determinantEqual (by simp [realDirections_diagonal])
    have hsub' : X - (X.2, X.2) ∈ realDirections (determinantEqual ι ℂ) :=
      (realTangentLieSubalgebra (determinantEqual ι ℂ) isClosed_determinantEqual).sub_mem hX hdiag
    have hsub : (X.1 - X.2, 0) ∈ realDirections (determinantEqual ι ℂ) :=
      (Prod.ext rfl (sub_self X.2) : X - (X.2, X.2) = (X.1 - X.2, 0)) ▸ hsub'
    have hsl : ∀ t : ℝ, (NormedSpace.exp (t • (X.1 - X.2))).det = 1 := by
      intro t
      have ht := congrArg Units.val (mem_determinantEqual_iff.mp (hsub t))
      have hdet2 : ((pairExp (t • (X.1 - X.2, (0 : Matrix ι ι ℂ)))).2.det : ℂ) = 1 := by
        simp [GeneralLinearGroup.val_det_apply]
      rw [hdet2, GeneralLinearGroup.val_det_apply, coe_fst_pairExp] at ht
      exact ht
    have htr := LieAlgebra.SpecialLinear.mem_sl_iff.mp
      ((Matrix.forall_det_exp_smul_eq_one_iff_mem_sl (X.1 - X.2)).mp hsl)
    rwa [Matrix.trace_sub, sub_eq_zero] at htr
  · intro htr t
    rw [mem_determinantEqual_iff, Units.ext_iff]
    simp only [GeneralLinearGroup.val_det_apply, coe_fst_pairExp, coe_snd_pairExp, Prod.smul_fst,
      Prod.smul_snd, Matrix.det_exp, Matrix.trace_smul, htr]

/-- **Classification of closed connected complex diagonal overgroups of `GL ι ℂ`.**
Every closed, preconnected subgroup `H ≤ GL ι ℂ × GL ι ℂ` containing `diagonal ι ℂ` whose real
exponential directions are closed under complex scalar multiplication is one of
`diagonal ι ℂ`, `scalarDiagonal ι ℂ`, `determinantEqual ι ℂ`, or `⊤`. -/
theorem connected_complex_overgroup (H : Subgroup (GL ι ℂ × GL ι ℂ))
    (hd : diagonal ι ℂ ≤ H) (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ)))
    (hconn : IsPreconnected (H : Set (GL ι ℂ × GL ι ℂ)))
    (hcomplex : ∀ X ∈ realDirections H, ∀ z : ℂ, pairExp (z • X) ∈ H) :
    H = diagonal ι ℂ ∨ H = scalarDiagonal ι ℂ ∨ H = determinantEqual ι ℂ ∨ H = ⊤ := by
  let L := complexTangentLieSubalgebra H hc hcomplex
  have hdL : diagonalLie ℂ ι ≤ L := by
    intro X hX
    exact realDirections_mono hd (by rwa [realDirections_diagonal])
  rcases eq_diagonalLie_or_eq_scalarDiagonalLie_or_eq_traceEqualLie_or_eq_top
      (two_ne_zero : (2 : ℂ) ≠ 0) L hdL with hL | hL | hL | hL
  · left
    exact eq_of_realDirections_eq hc hconn isClosed_diagonal isPreconnected_diagonal
      ((congrArg (SetLike.coe : LieSubalgebra ℂ _ → Set _) hL).trans realDirections_diagonal.symm)
  · right; left
    exact eq_of_realDirections_eq hc hconn isClosed_scalarDiagonal isPreconnected_scalarDiagonal
      ((congrArg (SetLike.coe : LieSubalgebra ℂ _ → Set _) hL).trans
        realDirections_scalarDiagonal.symm)
  · right; right; left
    exact eq_of_realDirections_eq hc hconn isClosed_determinantEqual
      isPreconnected_determinantEqual
      ((congrArg (SetLike.coe : LieSubalgebra ℂ _ → Set _) hL).trans
        realDirections_determinantEqual.symm)
  · right; right; right
    exact eq_of_realDirections_eq hc hconn isClosed_univ isPreconnected_univ_pair
      ((congrArg (SetLike.coe : LieSubalgebra ℂ _ → Set _) hL).trans realDirections_top.symm)

end LieBridge

end Exponential

end TauCeti.DiagonalOvergroups
