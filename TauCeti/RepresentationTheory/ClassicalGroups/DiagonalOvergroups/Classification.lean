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
-- Supplies `instance : PathConnectedSpace ℂˣ` for `instPathConnectedSpaceScalarDiagonal`.
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
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Diagonal

/-!
# Classification of connected complex diagonal overgroups of `GL ι ℂ`

Every closed, preconnected subgroup `H ≤ GL ι ℂ × GL ι ℂ` containing `diagonal ι ℂ` whose real
exponential directions `realDirections H` are closed under complex scalar multiplication equals one
of `diagonal ι ℂ`, `scalarDiagonal ι ℂ`, `determinantEqual ι ℂ`, or `⊤`
(`eq_diagonal_or_eq_scalarDiagonal_or_eq_determinantEqual_or_eq_top`).

1. Over any field `K` with `(2 : K) ≠ 0`, `L ↦ {Z | (Z, 0) ∈ L}` reduces `K`-Lie subalgebras of
   `Matrix ι ι K × Matrix ι ι K` containing `diagonalLie K ι` to Lie ideals of `gl ι K`, classifying
   them via `TauCeti.eq_bot_or_eq_center_or_eq_slIdeal_or_eq_top`.
2. Goursat normal-kernel coordinates and path connectivity of `GL ι ℂ`, `SL ι ℂ`, and `ℂˣ` make all
   four complex model subgroups closed and path-connected.
3. Pulling `H` back along `ContinuousMulEquiv.prodUnits` identifies `realDirections H` with
   `TauCeti.Lie.lieSubalgebraOfSubgroup`; `TauCeti.Lie.le_of_lieSubalgebraOfSubgroup_le` recovers
   `H` from its complex tangent Lie subalgebra.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222, 2015,
  Chapters 2–3.
-/

public section

open Matrix NormedSpace

namespace TauCeti.DiagonalOvergroups

attribute [local instance 100] LieRing.ofAssociativeRing

section LieClassification

variable (R ι : Type*) [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The diagonal Lie subalgebra `{(X, X)}` of `Matrix ι ι R × Matrix ι ι R`. -/
def diagonalLie : LieSubalgebra R (Matrix ι ι R × Matrix ι ι R) where
  carrier := {X | X.1 = X.2}
  add_mem' {_ _} hX hY := congrArg₂ (· + ·) hX hY
  zero_mem' := rfl
  smul_mem' c {_} hX := congrArg (c • ·) hX
  lie_mem' {_ _} hX hY := congrArg₂ (⁅·, ·⁆) hX hY

/-- The scalar-diagonal Lie subalgebra `{(c • 1 + Y, Y)}` of `Matrix ι ι R × Matrix ι ι R`. -/
def scalarDiagonalLie : LieSubalgebra R (Matrix ι ι R × Matrix ι ι R) where
  carrier := {X | ∃ c : R, X.1 = c • 1 + X.2}
  add_mem' := fun ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ =>
    ⟨c₁ + c₂, by rw [Prod.fst_add, Prod.snd_add, hc₁, hc₂, add_smul]; abel⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' r := fun ⟨c, hc⟩ =>
    ⟨r * c, by rw [Prod.smul_fst, Prod.smul_snd, hc, smul_add, mul_smul]⟩
  lie_mem' := by
    rintro X Y ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
    refine ⟨0, ?_⟩
    simp only [LieRing.of_associative_ring_bracket, Prod.fst_sub, Prod.snd_sub, Prod.fst_mul,
      Prod.snd_mul, zero_smul, zero_add]
    have h1 : c₁ • (c₂ • (1 : Matrix ι ι R)) = c₂ • (c₁ • 1) := by
      rw [smul_smul, smul_smul, mul_comm]
    rw [hc₁, hc₂]
    simp only [add_mul, mul_add, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_add, h1]
    abel

/-- The trace-equal Lie subalgebra `{(X, Y) | X.trace = Y.trace}`. -/
def traceEqualLie : LieSubalgebra R (Matrix ι ι R × Matrix ι ι R) where
  carrier := {X | X.1.trace = X.2.trace}
  add_mem' {_ _} hX hY := by simp_all
  zero_mem' := by simp
  smul_mem' c {_} hX := by simp_all
  lie_mem' {X Y} _ _ := by
    simp only [Set.mem_ofPred_eq, LieRing.of_associative_ring_bracket, Prod.fst_sub, Prod.snd_sub,
      Prod.fst_mul, Prod.snd_mul, Matrix.trace_sub, Matrix.trace_mul_comm X.1 Y.1,
      Matrix.trace_mul_comm X.2 Y.2, sub_self]

variable {R ι}

@[simp] theorem mem_diagonalLie_iff {X : Matrix ι ι R × Matrix ι ι R} :
    X ∈ diagonalLie R ι ↔ X.1 = X.2 := by rfl

@[simp] theorem mem_scalarDiagonalLie_iff {X : Matrix ι ι R × Matrix ι ι R} :
    X ∈ scalarDiagonalLie R ι ↔ ∃ c : R, X.1 = c • 1 + X.2 := by rfl

@[simp] theorem mem_traceEqualLie_iff {X : Matrix ι ι R × Matrix ι ι R} :
    X ∈ traceEqualLie R ι ↔ X.1.trace = X.2.trace := by rfl

/-- **Lie-algebra overgroup classification** over a field `K` with `(2 : K) ≠ 0`. -/
theorem eq_diagonalLie_or_eq_scalarDiagonalLie_or_eq_traceEqualLie_or_eq_top
    {K : Type*} [Field K] (htwo : (2 : K) ≠ 0)
    (L : LieSubalgebra K (Matrix ι ι K × Matrix ι ι K)) (hd : diagonalLie K ι ≤ L) :
    L = diagonalLie K ι ∨ L = scalarDiagonalLie K ι ∨ L = traceEqualLie K ι ∨ L = ⊤ := by
  let fstIdeal : LieIdeal K (Matrix ι ι K) :=
    { carrier := {Z | (Z, 0) ∈ L}
      add_mem' {A B} hA hB := by simpa using L.add_mem hA hB
      zero_mem' := L.zero_mem
      smul_mem' c {Z} hZ := by simpa using L.smul_mem c hZ
      lie_mem {A Z} hZ := by simpa using L.lie_mem (hd (rfl : (A, A).1 = (A, A).2)) hZ }
  have hmem (X : Matrix ι ι K × Matrix ι ι K) : X ∈ L ↔ X.1 - X.2 ∈ fstIdeal := by
    rcases X with ⟨X₁, X₂⟩
    have hdiag : (X₂, X₂) ∈ L := hd rfl
    exact ⟨fun hX => by simpa [fstIdeal] using L.sub_mem hX hdiag,
      fun hsub => by simpa using L.add_mem hsub hdiag⟩
  rcases TauCeti.eq_bot_or_eq_center_or_eq_slIdeal_or_eq_top fstIdeal htwo with hI | hI | hI | hI
  · exact Or.inl <| SetLike.ext fun X => by
      rw [hmem, hI, LieSubmodule.mem_bot, sub_eq_zero, mem_diagonalLie_iff]
  · refine Or.inr <| Or.inl <| SetLike.ext fun X => ?_
    rw [hmem, hI, TauCeti.mem_center_matrix_iff, mem_scalarDiagonalLie_iff]
    exact ⟨fun ⟨c, hc⟩ => ⟨c, eq_add_of_sub_eq hc⟩, fun ⟨c, hc⟩ => ⟨c, sub_eq_of_eq_add hc⟩⟩
  · exact Or.inr <| Or.inr <| Or.inl <| SetLike.ext fun X => by
      rw [hmem, hI, TauCeti.mem_slIdeal_iff, Matrix.trace_sub, sub_eq_zero, mem_traceEqualLie_iff]
  · exact Or.inr <| Or.inr <| Or.inr <| SetLike.ext fun X => by simp [hmem, hI]

end LieClassification

section ModelTopology

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
/-- For a `T₂` space `R`, `diagonal ι R` is closed in `GL ι R × GL ι R`. -/
theorem isClosed_diagonal [T2Space R] : IsClosed (diagonal ι R : Set (GL ι R × GL ι R)) := by
  rw [show (diagonal ι R : Set (GL ι R × GL ι R)) = {p | p.1 = p.2} from
    Set.ext fun _ => mem_diagonal_iff]
  exact isClosed_eq continuous_fst continuous_snd

/-- Over a `T₂` topological commutative ring `R`, `scalarDiagonal ι R` is closed in
`GL ι R × GL ι R`. -/
theorem isClosed_scalarDiagonal [T2Space R] :
    IsClosed (scalarDiagonal ι R : Set (GL ι R × GL ι R)) := by
  rw [Subgroup.isClosed_iff_isClosed_goursatFst graph_id_le_scalarDiagonal,
    goursatFst_scalarDiagonal]
  exact Subgroup.isClosed_center

/-- Over a `T₂` topological commutative ring `R`, `determinantEqual ι R` is closed in
`GL ι R × GL ι R`. -/
theorem isClosed_determinantEqual [T2Space R] :
    IsClosed (determinantEqual ι R : Set (GL ι R × GL ι R)) := by
  rw [Subgroup.isClosed_iff_isClosed_goursatFst graph_id_le_determinantEqual,
    goursatFst_determinantEqual]
  exact MonoidHom.coe_range (SpecialLinearGroup.toGL (n := ι) (R := R)) ▸
    SpecialLinearGroup.isClosedEmbedding_toGL.isClosed_range

/-- `diagonal ι ℂ` is path connected. -/
instance instPathConnectedSpaceDiagonal : PathConnectedSpace (diagonal ι ℂ) := by
  rw [Subgroup.pathConnectedSpace_iff_pathConnectedSpace_goursatFst
    (diagonal_eq_graph_id (ι := ι) (R := ℂ)).ge, goursatFst_diagonal]
  exact ⟨⟨1⟩, fun x y => Subsingleton.elim x y ▸ Joined.refl x⟩

/-- `scalarDiagonal ι ℂ` is path connected. -/
instance instPathConnectedSpaceScalarDiagonal : PathConnectedSpace (scalarDiagonal ι ℂ) := by
  rw [Subgroup.pathConnectedSpace_iff_pathConnectedSpace_goursatFst graph_id_le_scalarDiagonal,
    goursatFst_scalarDiagonal, GeneralLinearGroup.center_eq_range_scalar]
  exact (GeneralLinearGroup.scalar ι).rangeRestrict_surjective.pathConnectedSpace
    (GeneralLinearGroup.continuous_scalar.subtype_mk _)

/-- `determinantEqual ι ℂ` is path connected. -/
instance instPathConnectedSpaceDeterminantEqual : PathConnectedSpace (determinantEqual ι ℂ) := by
  rw [Subgroup.pathConnectedSpace_iff_pathConnectedSpace_goursatFst graph_id_le_determinantEqual,
    goursatFst_determinantEqual]
  exact (SpecialLinearGroup.toGL (n := ι) (R := ℂ)).rangeRestrict_surjective.pathConnectedSpace
    (SpecialLinearGroup.isClosedEmbedding_toGL.continuous.subtype_mk _)

end ModelTopology

section Exponential

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Componentwise matrix exponential** `Matrix ι ι ℂ × Matrix ι ι ℂ → GL ι ℂ × GL ι ℂ`. -/
noncomputable def pairExp (X : Matrix ι ι ℂ × Matrix ι ι ℂ) : GL ι ℂ × GL ι ℂ :=
  ((Matrix.isUnit_exp X.1).unit, (Matrix.isUnit_exp X.2).unit)

@[simp] theorem coe_fst_pairExp (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    ((pairExp X).1 : Matrix ι ι ℂ) = NormedSpace.exp X.1 := (Matrix.isUnit_exp X.1).unit_spec

@[simp] theorem coe_snd_pairExp (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    ((pairExp X).2 : Matrix ι ι ℂ) = NormedSpace.exp X.2 := (Matrix.isUnit_exp X.2).unit_spec

@[simp] theorem pairExp_zero : pairExp (0 : Matrix ι ι ℂ × Matrix ι ι ℂ) = 1 :=
  Prod.ext (Units.ext (by simp)) (Units.ext (by simp))

theorem pairExp_add_of_commute {X Y : Matrix ι ι ℂ × Matrix ι ι ℂ} (h : Commute X Y) :
    pairExp (X + Y) = pairExp X * pairExp Y :=
  Prod.ext (Units.ext (by simp [Matrix.exp_add_of_commute X.1 Y.1 (congrArg Prod.fst h)]))
    (Units.ext (by simp [Matrix.exp_add_of_commute X.2 Y.2 (congrArg Prod.snd h)]))

@[simp] theorem pairExp_add_smul (z w : ℂ) (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    pairExp ((z + w) • X) = pairExp (z • X) * pairExp (w • X) := by
  rw [add_smul]; exact pairExp_add_of_commute (((Commute.refl X).smul_left z).smul_right w)

@[simp] theorem pairExp_add_real_smul (s t : ℝ) (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    pairExp ((s + t) • X) = pairExp (s • X) * pairExp (t • X) := by
  rw [← algebraMap_smul ℂ (s + t) X, map_add, pairExp_add_smul, algebraMap_smul, algebraMap_smul]

@[simp] theorem pairExp_neg (X : Matrix ι ι ℂ × Matrix ι ι ℂ) : pairExp (-X) = (pairExp X)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by
    rw [← pairExp_add_of_commute (Commute.refl X).neg_left, neg_add_cancel, pairExp_zero])

/-- **Real exponential directions** of `H ≤ GL ι ℂ × GL ι ℂ`. -/
def realDirections (H : Subgroup (GL ι ℂ × GL ι ℂ)) : Set (Matrix ι ι ℂ × Matrix ι ι ℂ) :=
  {X | ∀ t : ℝ, pairExp (t • X) ∈ H}

@[simp] theorem mem_realDirections_iff {H : Subgroup (GL ι ℂ × GL ι ℂ)}
    {X : Matrix ι ι ℂ × Matrix ι ι ℂ} :
    X ∈ realDirections H ↔ ∀ t : ℝ, pairExp (t • X) ∈ H := by rfl

theorem realDirections_mono {H₁ H₂ : Subgroup (GL ι ℂ × GL ι ℂ)} (h : H₁ ≤ H₂) :
    realDirections H₁ ≤ realDirections H₂ := fun _ hX t => h (hX t)

@[simp] theorem realDirections_top :
    realDirections (⊤ : Subgroup (GL ι ℂ × GL ι ℂ)) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ => Subgroup.mem_top _

/-- **Complex closure of `realDirections H` is equivalent to `Complex.I`-invariance.** -/
theorem forall_pairExp_complex_smul_mem_iff_I_smul_mem (H : Subgroup (GL ι ℂ × GL ι ℂ)) :
    (∀ X ∈ realDirections H, ∀ z : ℂ, pairExp (z • X) ∈ H) ↔
      ∀ X ∈ realDirections H, Complex.I • X ∈ realDirections H := by
  refine ⟨fun h X hX t => ?_, fun hI X hX z => ?_⟩
  · rw [← algebraMap_smul ℂ t (Complex.I • X), smul_smul, Complex.coe_algebraMap]
    exact h X hX _
  · have hz : z • X = z.re • X + z.im • (Complex.I • X) := by
      rw [← algebraMap_smul ℂ z.re X, ← algebraMap_smul ℂ z.im (Complex.I • X), smul_smul,
        Complex.coe_algebraMap, ← add_smul, Complex.re_add_im]
    have hcomm : Commute (z.re • X) (z.im • (Complex.I • X)) := by
      rw [← algebraMap_smul ℂ z.re X, ← algebraMap_smul ℂ z.im (Complex.I • X), smul_smul]
      exact ((Commute.refl X).smul_left _).smul_right _
    rw [hz, pairExp_add_of_commute hcomm]
    exact H.mul_mem (hX z.re) (hI X hX z.im)

private theorem isPreconnected_diagonal : IsPreconnected (SetLike.coe (diagonal ι ℂ)) :=
  isPreconnected_iff_preconnectedSpace.mpr (inferInstanceAs (PreconnectedSpace (diagonal ι ℂ)))

private theorem isPreconnected_scalarDiagonal :
    IsPreconnected (SetLike.coe (scalarDiagonal ι ℂ)) :=
  isPreconnected_iff_preconnectedSpace.mpr
    (inferInstanceAs (PreconnectedSpace (scalarDiagonal ι ℂ)))

private theorem isPreconnected_determinantEqual :
    IsPreconnected (SetLike.coe (determinantEqual ι ℂ)) :=
  isPreconnected_iff_preconnectedSpace.mpr
    (inferInstanceAs (PreconnectedSpace (determinantEqual ι ℂ)))

section LieBridge

open Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator

attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance] TauCeti.normedAlgebraRatOfReal

private theorem prodUnits_expUnit_eq_pairExp (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    ContinuousMulEquiv.prodUnits (Matrix ι ι ℂ) (Matrix ι ι ℂ) (TauCeti.expUnit X) =
      pairExp X := by
  rw [ContinuousMulEquiv.prodUnits_apply]
  -- Entrywise and `L∞` operator-norm topologies on `Matrix ι ι ℂ` are definitionally equal.
  refine Prod.ext (Units.ext ?_) (Units.ext ?_) <;>
    simp [TauCeti.expUnit_coe, Prod.fst_exp, Prod.snd_exp] <;> rfl

private theorem mem_realDirections_iff_mem_lieSubalgebraOfSubgroup
    {H : Subgroup (GL ι ℂ × GL ι ℂ)} (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ)))
    (X : Matrix ι ι ℂ × Matrix ι ι ℂ) :
    X ∈ realDirections H ↔
      (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix ι ι ℂ × Matrix ι ι ℂ)).symm X ∈
        TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Matrix ι ι ℂ × Matrix ι ι ℂ))
          (H.comap (MonoidHom.ofClass
            (ContinuousMulEquiv.prodUnits (Matrix ι ι ℂ) (Matrix ι ι ℂ)))) := by
  rw [TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff
    (hc.preimage (map_continuous (ContinuousMulEquiv.prodUnits (Matrix ι ι ℂ) (Matrix ι ι ℂ)))),
    mem_realDirections_iff]
  exact forall_congr' fun t => by
    rw [Subgroup.mem_comap, MonoidHom.coe_ofClass, prodUnits_expUnit_eq_pairExp]

/-- **Real tangent Lie subalgebra** of a closed subgroup `H ≤ GL ι ℂ × GL ι ℂ`. -/
noncomputable def realTangentLieSubalgebra (H : Subgroup (GL ι ℂ × GL ι ℂ))
    (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ))) :
    LieSubalgebra ℝ (Matrix ι ι ℂ × Matrix ι ι ℂ) where
  carrier := realDirections H
  add_mem' {X Y} hX hY :=
    (mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc (X + Y)).mpr <| by
      rw [map_add]
      exact LieSubalgebra.add_mem _
        ((mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc X).mp hX)
        ((mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc Y).mp hY)
  zero_mem' := by simp [realDirections]
  smul_mem' r {X} hX t := by rw [smul_smul]; exact hX (t * r)
  lie_mem' {X Y} hX hY := by
    rw [mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc,
      (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix ι ι ℂ × Matrix ι ι ℂ)).symm.map_lie]
    exact LieSubalgebra.lie_mem _
      ((mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc X).mp hX)
      ((mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc Y).mp hY)

@[simp] theorem mem_realTangentLieSubalgebra_iff {H : Subgroup (GL ι ℂ × GL ι ℂ)}
    (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ))) {X : Matrix ι ι ℂ × Matrix ι ι ℂ} :
    X ∈ realTangentLieSubalgebra H hc ↔ X ∈ realDirections H := by rfl

/-- **Complex tangent Lie subalgebra** of a closed complex-closed subgroup `H ≤ GL ι ℂ × GL ι ℂ`. -/
noncomputable def complexTangentLieSubalgebra (H : Subgroup (GL ι ℂ × GL ι ℂ))
    (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ)))
    (hcomplex : ∀ X ∈ realDirections H, ∀ z : ℂ, pairExp (z • X) ∈ H) :
    LieSubalgebra ℂ (Matrix ι ι ℂ × Matrix ι ι ℂ) where
  carrier := realDirections H
  add_mem' := (realTangentLieSubalgebra H hc).add_mem
  zero_mem' := (realTangentLieSubalgebra H hc).zero_mem
  smul_mem' z {X} hX t := by
    rw [← algebraMap_smul ℂ t (z • X), smul_smul, Complex.coe_algebraMap]
    exact hcomplex X hX _
  lie_mem' := (realTangentLieSubalgebra H hc).lie_mem

@[simp] theorem mem_complexTangentLieSubalgebra_iff {H : Subgroup (GL ι ℂ × GL ι ℂ)}
    (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ)))
    (hcomplex : ∀ X ∈ realDirections H, ∀ z : ℂ, pairExp (z • X) ∈ H)
    {X : Matrix ι ι ℂ × Matrix ι ι ℂ} :
    X ∈ complexTangentLieSubalgebra H hc hcomplex ↔ X ∈ realDirections H := by rfl

/-- Inclusion of closed subgroups from inclusion of `realDirections` when `H₁` is preconnected. -/
theorem le_of_realDirections_le {H₁ H₂ : Subgroup (GL ι ℂ × GL ι ℂ)}
    (hc₁ : IsClosed (H₁ : Set (GL ι ℂ × GL ι ℂ)))
    (hconn₁ : IsPreconnected (H₁ : Set (GL ι ℂ × GL ι ℂ)))
    (hc₂ : IsClosed (H₂ : Set (GL ι ℂ × GL ι ℂ)))
    (hle : realDirections H₁ ≤ realDirections H₂) :
    H₁ ≤ H₂ := by
  let e := ContinuousMulEquiv.prodUnits (Matrix ι ι ℂ) (Matrix ι ι ℂ)
  have hconnK₁ : IsPreconnected (SetLike.coe (H₁.comap (MonoidHom.ofClass e))) := by
    have himg : e.symm '' (H₁ : Set _) = SetLike.coe (H₁.comap (MonoidHom.ofClass e)) :=
      Set.ext fun u => ⟨by rintro ⟨_, hp, rfl⟩; simpa using hp, fun hu => ⟨e u, hu, by simp⟩⟩
    exact himg ▸ hconn₁.image _ e.symm.continuous.continuousOn
  have hKle := TauCeti.Lie.le_of_lieSubalgebraOfSubgroup_le
    (I := 𝓘(ℝ, Matrix ι ι ℂ × Matrix ι ι ℂ))
    (hc₁.preimage (map_continuous e)) hconnK₁ (hc₂.preimage (map_continuous e)) fun D hD => by
      let f := TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix ι ι ℂ × Matrix ι ι ℂ)
      rw [← f.symm_apply_apply D] at hD ⊢
      exact (mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc₂ (f D)).mp
        (hle ((mem_realDirections_iff_mem_lieSubalgebraOfSubgroup hc₁ (f D)).mpr hD))
  intro p hp
  have hp'' : e (e.symm p) ∈ H₂ := hKle (show e (e.symm p) ∈ H₁ by rwa [e.apply_symm_apply])
  rwa [e.apply_symm_apply] at hp''

/-- Closed, preconnected subgroups of `GL ι ℂ × GL ι ℂ` with the same `realDirections` are equal. -/
theorem eq_of_realDirections_eq {H₁ H₂ : Subgroup (GL ι ℂ × GL ι ℂ)}
    (hc₁ : IsClosed (H₁ : Set (GL ι ℂ × GL ι ℂ)))
    (hconn₁ : IsPreconnected (H₁ : Set (GL ι ℂ × GL ι ℂ)))
    (hc₂ : IsClosed (H₂ : Set (GL ι ℂ × GL ι ℂ)))
    (hconn₂ : IsPreconnected (H₂ : Set (GL ι ℂ × GL ι ℂ)))
    (heq : realDirections H₁ = realDirections H₂) :
    H₁ = H₂ :=
  le_antisymm (le_of_realDirections_le hc₁ hconn₁ hc₂ heq.le)
    (le_of_realDirections_le hc₂ hconn₂ hc₁ heq.ge)

/-- The real exponential directions of `diagonal ι ℂ` form `diagonalLie ℂ ι`. -/
@[simp] theorem realDirections_diagonal :
    realDirections (diagonal ι ℂ) = (diagonalLie ℂ ι : Set (Matrix ι ι ℂ × Matrix ι ι ℂ)) := by
  ext X
  simp only [mem_realDirections_iff, mem_diagonal_iff, Units.ext_iff, coe_fst_pairExp,
    coe_snd_pairExp, Prod.smul_fst, Prod.smul_snd, SetLike.mem_coe, mem_diagonalLie_iff]
  exact ⟨TauCeti.eq_of_forall_exp_smul_eq, fun h _ => by rw [h]⟩

private theorem sub_zero_mem_realDirections {H : Subgroup (GL ι ℂ × GL ι ℂ)}
    (hd : diagonal ι ℂ ≤ H) (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ)))
    {X : Matrix ι ι ℂ × Matrix ι ι ℂ} (hX : X ∈ realDirections H) :
    (X.1 - X.2, 0) ∈ realDirections H :=
  (Prod.ext rfl (sub_self X.2) : X - (X.2, X.2) = (X.1 - X.2, 0)) ▸
    (realTangentLieSubalgebra H hc).sub_mem hX
      (realDirections_mono hd (by simp [realDirections_diagonal]))

private theorem mem_center_of_pairExp_sub_mem_scalarDiagonal {Z : Matrix ι ι ℂ}
    (hsub : (Z, 0) ∈ realDirections (scalarDiagonal ι ℂ)) :
    Z ∈ LieAlgebra.center ℂ (Matrix ι ι ℂ) := by
  have hcenter (t : ℝ) : TauCeti.expUnit (t • Z) ∈ Subgroup.center (Matrix ι ι ℂ)ˣ := by
    obtain ⟨u, hu⟩ := mem_scalarDiagonal_iff.mp (hsub t)
    have heq : TauCeti.expUnit (t • Z) = GeneralLinearGroup.scalar ι u := Units.ext <| by
      rw [TauCeti.expUnit_coe]
      exact (coe_fst_pairExp (t • (Z, (0 : Matrix ι ι ℂ)))).symm.trans
        (by simpa [show (pairExp (t • (Z, (0 : Matrix ι ι ℂ)))).2 = 1 from Units.ext (by simp)]
          using congrArg Units.val hu)
    exact heq ▸ GeneralLinearGroup.center_eq_range_scalar.ge ⟨u, rfl⟩
  let e := TauCeti.Lie.unitsLieAlgebraLieEquiv (R := Matrix ι ι ℂ)
  have hzc := TauCeti.Lie.lieSubalgebraOfSubgroup_center_le
    ((TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff
      Subgroup.isClosed_center Z).mpr hcenter)
  refine (LieModule.mem_maxTrivSubmodule ℂ _ _ _).mpr fun B => ?_
  have h1 := congrArg e ((LieModule.mem_maxTrivSubmodule ℝ _ _ _).mp hzc (e.symm B))
  rwa [e.map_lie, e.apply_symm_apply, e.apply_symm_apply, map_zero] at h1

/-- The real exponential directions of `scalarDiagonal ι ℂ` form `scalarDiagonalLie ℂ ι`. -/
@[simp] theorem realDirections_scalarDiagonal :
    realDirections (scalarDiagonal ι ℂ) =
      (scalarDiagonalLie ℂ ι : Set (Matrix ι ι ℂ × Matrix ι ι ℂ)) := by
  ext X
  simp only [SetLike.mem_coe, mem_scalarDiagonalLie_iff]
  refine ⟨fun hX => ?_, fun ⟨c, hc⟩ t => mem_scalarDiagonal_iff.mpr
    ⟨(NormedSpace.isUnit_exp (t • c)).unit, Units.ext ?_⟩⟩
  · obtain ⟨c, hc⟩ := TauCeti.mem_center_matrix_iff.mp
      (mem_center_of_pairExp_sub_mem_scalarDiagonal
        (sub_zero_mem_realDirections diagonal_le_scalarDiagonal isClosed_scalarDiagonal hX))
    exact ⟨c, eq_add_of_sub_eq hc⟩
  · have hsmul : t • X.1 = (t • c) • (1 : Matrix ι ι ℂ) + t • X.2 := by
      rw [hc, smul_add, ← algebraMap_smul ℂ t (c • 1), smul_smul, ← Algebra.smul_def]
    simp only [Prod.smul_fst, Prod.smul_snd, coe_fst_pairExp, coe_snd_pairExp, Units.val_mul]
    rw [hsmul, Matrix.exp_add_of_commute _ _ ((Commute.one_left (t • X.2)).smul_left (t • c)),
      Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Pi.exp_def, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply]
    exact congrArg (· * _)
      (congrArg Matrix.diagonal (funext fun _ => (NormedSpace.isUnit_exp (t • c)).unit_spec.symm))

/-- The real exponential directions of `determinantEqual ι ℂ` form `traceEqualLie ℂ ι`. -/
@[simp] theorem realDirections_determinantEqual :
    realDirections (determinantEqual ι ℂ) =
      (traceEqualLie ℂ ι : Set (Matrix ι ι ℂ × Matrix ι ι ℂ)) := by
  ext X
  simp only [SetLike.mem_coe, mem_traceEqualLie_iff]
  refine ⟨fun hX => ?_, fun htr t => ?_⟩
  · have hsub := sub_zero_mem_realDirections diagonal_le_determinantEqual
      isClosed_determinantEqual hX
    have hsl (t : ℝ) : (NormedSpace.exp (t • (X.1 - X.2))).det = 1 := by
      have ht := congrArg Units.val (mem_determinantEqual_iff.mp (hsub t))
      have hdet2 : ((pairExp (t • (X.1 - X.2, (0 : Matrix ι ι ℂ)))).2.det : ℂ) = 1 := by
        simp [GeneralLinearGroup.val_det_apply]
      rwa [hdet2, GeneralLinearGroup.val_det_apply, coe_fst_pairExp] at ht
    simpa [Matrix.trace_sub, sub_eq_zero] using LieAlgebra.SpecialLinear.mem_sl_iff.mp
      ((Matrix.forall_det_exp_smul_eq_one_iff_mem_sl (X.1 - X.2)).mp hsl)
  · simp [mem_determinantEqual_iff, Units.ext_iff, GeneralLinearGroup.val_det_apply,
      Matrix.det_exp, htr]

/-- **Classification of closed connected diagonal overgroups of `GL ι ℂ` whose real exponential
directions are closed under complex scalar multiplication:** every closed, preconnected subgroup
`H ≤ GL ι ℂ × GL ι ℂ` containing `diagonal ι ℂ` with `realDirections H` closed under complex
scaling equals `diagonal ι ℂ`, `scalarDiagonal ι ℂ`, `determinantEqual ι ℂ`, or `⊤`. -/
theorem eq_diagonal_or_eq_scalarDiagonal_or_eq_determinantEqual_or_eq_top
    (H : Subgroup (GL ι ℂ × GL ι ℂ))
    (hd : diagonal ι ℂ ≤ H) (hc : IsClosed (H : Set (GL ι ℂ × GL ι ℂ)))
    (hconn : IsPreconnected (H : Set (GL ι ℂ × GL ι ℂ)))
    (hcomplex : ∀ X ∈ realDirections H, ∀ z : ℂ, pairExp (z • X) ∈ H) :
    H = diagonal ι ℂ ∨ H = scalarDiagonal ι ℂ ∨ H = determinantEqual ι ℂ ∨ H = ⊤ := by
  have : PathConnectedSpace (GL ι ℂ) := TauCeti.instPathConnectedSpaceMatrixGeneralLinearGroup
  let L := complexTangentLieSubalgebra H hc hcomplex
  have hdL : diagonalLie ℂ ι ≤ L := fun _ hX =>
    realDirections_mono hd (by rwa [realDirections_diagonal])
  rcases eq_diagonalLie_or_eq_scalarDiagonalLie_or_eq_traceEqualLie_or_eq_top
      (two_ne_zero : (2 : ℂ) ≠ 0) L hdL with hL | hL | hL | hL
  · exact Or.inl <| eq_of_realDirections_eq hc hconn isClosed_diagonal isPreconnected_diagonal
      ((congrArg (SetLike.coe : LieSubalgebra ℂ _ → Set _) hL).trans realDirections_diagonal.symm)
  · exact Or.inr <| Or.inl <| eq_of_realDirections_eq hc hconn isClosed_scalarDiagonal
      isPreconnected_scalarDiagonal
      ((congrArg (SetLike.coe : LieSubalgebra ℂ _ → Set _) hL).trans
        realDirections_scalarDiagonal.symm)
  · exact Or.inr <| Or.inr <| Or.inl <| eq_of_realDirections_eq hc hconn isClosed_determinantEqual
      isPreconnected_determinantEqual
      ((congrArg (SetLike.coe : LieSubalgebra ℂ _ → Set _) hL).trans
        realDirections_determinantEqual.symm)
  · exact Or.inr <| Or.inr <| Or.inr <| eq_of_realDirections_eq hc hconn isClosed_univ
      isPreconnected_univ
      ((congrArg (SetLike.coe : LieSubalgebra ℂ _ → Set _) hL).trans realDirections_top.symm)

end LieBridge

end Exponential

end TauCeti.DiagonalOvergroups
