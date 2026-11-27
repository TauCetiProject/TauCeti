/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.DiagonalOvergroups.Classification
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Topology.Algebra.Group.Matrix
import TauCeti.Analysis.Matrix.GeneralLinearGroup.Connected
import TauCeti.Analysis.Matrix.SpecialLinearGroup.Connected
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unique
import TauCeti.Topology.Algebra.Group.Goursat
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.Diagonal

/-!
# Rank phenomena and real counterexample for diagonal overgroups of `GL`

Complements `TauCeti.RepresentationTheory.ClassicalGroups.DiagonalOvergroups.Classification` with:
* rank `0` (`[IsEmpty ι]`): all four subgroups equal `⊤`;
* rank `1` (`[Unique ι]`): `determinantEqual ι R = diagonal ι R` and `scalarDiagonal ι R = ⊤`;
* rank `≥ 2`: strict inclusions (`diagonal_lt_scalarDiagonal`, `determinantEqual_lt_top` over any
  `CommRing R` with `[Nontrivial Rˣ]`; `diagonal_lt_determinantEqual`, `scalarDiagonal_lt_top` over
  any `[Nontrivial R]`), non-containment `not_scalarDiagonal_le_determinantEqual` over any
  characteristic-zero field, join `scalarDiagonal_sup_determinantEqual = ⊤` over any algebraically
  closed field, and disconnected intersection over `ℂ`;
* `determinantModulusOne ι` (`{(g, h) | ‖(determinantRatio ι ℂ (g, h) : ℂ)‖ = 1}`): for
  `[Nonempty ι]`, a closed, path-connected subgroup containing `diagonal ι ℂ` that strictly contains
  `determinantEqual ι ℂ` and is not one of the four models in
  `eq_diagonal_or_eq_scalarDiagonal_or_eq_determinantEqual_or_eq_top`, because it fails the
  complex-closure hypothesis (`not_forall_pairExp_complex_smul_mem_determinantModulusOne`).

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222, 2015,
  Chapters 1–3.
-/

public section

open Matrix NormedSpace

namespace TauCeti.DiagonalOvergroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- In rank `0` (`[IsEmpty ι]`), `diagonal ι R` equals `⊤`. -/
@[simp] theorem diagonal_eq_top_of_isEmpty [IsEmpty ι] : diagonal ι R = ⊤ :=
  eq_top_iff.mpr fun p _ => mem_diagonal_iff.mpr (Subsingleton.elim p.1 p.2)

/-- In rank `0` (`[IsEmpty ι]`), `scalarDiagonal ι R` equals `⊤`. -/
@[simp] theorem scalarDiagonal_eq_top_of_isEmpty [IsEmpty ι] : scalarDiagonal ι R = ⊤ :=
  top_unique (diagonal_eq_top_of_isEmpty (ι := ι) (R := R) ▸ diagonal_le_scalarDiagonal)

/-- In rank `0` (`[IsEmpty ι]`), `determinantEqual ι R` equals `⊤`. -/
@[simp] theorem determinantEqual_eq_top_of_isEmpty [IsEmpty ι] : determinantEqual ι R = ⊤ :=
  top_unique (diagonal_eq_top_of_isEmpty (ι := ι) (R := R) ▸ diagonal_le_determinantEqual)

/-- In rank `1` (`[Unique ι]`), `determinantEqual ι R` collapses to `diagonal ι R`. -/
@[simp] theorem determinantEqual_eq_diagonal_of_unique [Unique ι] :
    determinantEqual ι R = diagonal ι R := by
  refine le_antisymm (fun p hp => mem_diagonal_iff.mpr ?_) diagonal_le_determinantEqual
  rw [GeneralLinearGroup.eq_scalar_det p.1, GeneralLinearGroup.eq_scalar_det p.2,
    mem_determinantEqual_iff.mp hp]

/-- In rank `1` (`[Unique ι]`), `scalarDiagonal ι R` equals `⊤`. -/
@[simp] theorem scalarDiagonal_eq_top_of_unique [Unique ι] : scalarDiagonal ι R = ⊤ :=
  eq_top_iff.mpr fun p _ => mem_scalarDiagonal_iff.mpr
    ⟨(p.1 / p.2).det, by rw [← GeneralLinearGroup.eq_scalar_det (p.1 / p.2), div_mul_cancel]⟩

/-- Membership in `scalarDiagonal ι R ⊓ determinantEqual ι R`: pairs differing by an `|ι|`-th root
of unity scalar. -/
theorem mem_scalarDiagonal_inf_determinantEqual_iff {p : GL ι R × GL ι R} :
    p ∈ scalarDiagonal ι R ⊓ determinantEqual ι R ↔
      ∃ u : Rˣ, u ^ Fintype.card ι = 1 ∧ p.1 = GeneralLinearGroup.scalar ι u * p.2 := by
  rw [Subgroup.mem_inf, mem_scalarDiagonal_iff, mem_determinantEqual_iff]
  refine ⟨fun ⟨⟨u, hu⟩, hdet⟩ => ⟨u, ?_, hu⟩,
    fun ⟨u, hu1, hu⟩ => ⟨⟨u, hu⟩, by rw [hu, map_mul, GeneralLinearGroup.det_scalar, hu1, one_mul]⟩⟩
  rw [hu, map_mul, GeneralLinearGroup.det_scalar] at hdet
  exact mul_right_cancel (hdet.trans (one_mul p.2.det).symm)

/-- Over a characteristic-zero field `K` with nonempty `ι`, `scalarDiagonal ι K` is not contained in
`determinantEqual ι K`. -/
theorem not_scalarDiagonal_le_determinantEqual {K : Type*} [Field K] [CharZero K] [Nonempty ι] :
    ¬ (scalarDiagonal ι K ≤ determinantEqual ι K) := fun hle => by
  let u : Kˣ := Units.mk0 2 two_ne_zero
  have hdet := congrArg Units.val (mem_determinantEqual_iff.mp
    (hle ((mem_scalarDiagonal_iff (p := (GeneralLinearGroup.scalar ι u, 1))).mpr
      ⟨u, (mul_one _).symm⟩)))
  simp only [u, map_one, GeneralLinearGroup.det_scalar, Units.val_pow_eq_pow_val, Units.val_one,
    Units.val_mk0] at hdet
  exact (Nat.one_lt_two_pow Fintype.card_ne_zero).ne'
    (Nat.cast_injective (R := K) (by simpa [Nat.cast_pow] using hdet))

/-- For nonempty `ι` and nontrivial `Rˣ`, `diagonal ι R` is strictly contained in
`scalarDiagonal ι R`. -/
theorem diagonal_lt_scalarDiagonal [Nonempty ι] [Nontrivial Rˣ] :
    diagonal ι R < scalarDiagonal ι R := by
  refine lt_of_le_of_ne diagonal_le_scalarDiagonal fun h => ?_
  obtain ⟨u, hu⟩ := exists_ne (1 : Rˣ)
  have hmem : (GeneralLinearGroup.scalar ι u, 1) ∈ diagonal ι R :=
    h ▸ (mem_scalarDiagonal_iff (p := (GeneralLinearGroup.scalar ι u, 1))).mpr
      ⟨u, (mul_one _).symm⟩
  exact hu (GeneralLinearGroup.scalar_injective ((mem_diagonal_iff.mp hmem).trans (map_one _).symm))

/-- For `|ι| ≥ 2` and nontrivial `R`, `diagonal ι R` is strictly contained in
`determinantEqual ι R`. -/
theorem diagonal_lt_determinantEqual [Nontrivial ι] [Nontrivial R] :
    diagonal ι R < determinantEqual ι R :=
  lt_of_le_of_ne diagonal_le_determinantEqual fun h =>
    not_determinantEqual_le_scalarDiagonal (h ▸ diagonal_le_scalarDiagonal)

/-- For nonempty `ι` and nontrivial `Rˣ`, `determinantEqual ι R` is strictly contained in `⊤`. -/
theorem determinantEqual_lt_top [Nonempty ι] [Nontrivial Rˣ] : determinantEqual ι R < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  obtain ⟨u, hu⟩ := exists_ne (1 : Rˣ)
  obtain ⟨g, hg⟩ := GeneralLinearGroup.det_surjective (n := ι) u
  have hdet := mem_determinantEqual_iff.mp (htop ▸ Subgroup.mem_top (g, 1))
  exact hu (by simpa [hg] using hdet)

/-- For `|ι| ≥ 2` and nontrivial `R`, `scalarDiagonal ι R` is strictly contained in `⊤`. -/
theorem scalarDiagonal_lt_top [Nontrivial ι] [Nontrivial R] : scalarDiagonal ι R < ⊤ :=
  lt_top_iff_ne_top.mpr scalarDiagonal_ne_top

/-- **For `|ι| ≥ 2`, `scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ` is not connected.** -/
theorem not_isPreconnected_scalarDiagonal_inf_determinantEqual [Nontrivial ι] :
    ¬ IsPreconnected ((scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ :
      Subgroup (GL ι ℂ × GL ι ℂ)) : Set (GL ι ℂ × GL ι ℂ)) := fun hconn => by
  have hcomplex : ∀ X ∈ realDirections (scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ),
      ∀ z : ℂ, pairExp (z • X) ∈ scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ := fun X hX z => by
    have hz1 : z • X ∈ realDirections (scalarDiagonal ι ℂ) := by
      rw [realDirections_scalarDiagonal]; exact (scalarDiagonalLie ℂ ι).smul_mem z
        (by rw [← SetLike.mem_coe, ← realDirections_scalarDiagonal]
            exact realDirections_mono inf_le_left hX)
    have hz2 : z • X ∈ realDirections (determinantEqual ι ℂ) := by
      rw [realDirections_determinantEqual]; exact (traceEqualLie ℂ ι).smul_mem z
        (by rw [← SetLike.mem_coe, ← realDirections_determinantEqual]
            exact realDirections_mono inf_le_right hX)
    exact ⟨by simpa using mem_realDirections_iff.mp hz1 1,
      by simpa using mem_realDirections_iff.mp hz2 1⟩
  rcases eq_diagonal_or_eq_scalarDiagonal_or_eq_determinantEqual_or_eq_top _
      (le_inf diagonal_le_scalarDiagonal diagonal_le_determinantEqual)
      (isClosed_scalarDiagonal.inter isClosed_determinantEqual)
      hconn hcomplex with heq | heq | heq | heq
  · have : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ (Fintype.card ι)
    let u : ℂˣ := (hζ.isUnit (NeZero.ne _)).unit
    have hu : IsPrimitiveRoot u (Fintype.card ι) := IsPrimitiveRoot.coe_units_iff.mp hζ
    have hmem : (GeneralLinearGroup.scalar ι u, (1 : GL ι ℂ)) ∈ diagonal ι ℂ :=
      heq ▸ mem_scalarDiagonal_inf_determinantEqual_iff.mpr ⟨u, hu.pow_eq_one, by simp⟩
    exact hu.ne_one Fintype.one_lt_card
      (GeneralLinearGroup.scalar_injective ((mem_diagonal_iff.mp hmem).trans (map_one _).symm))
  · exact not_scalarDiagonal_le_determinantEqual (heq ▸ inf_le_right)
  · exact not_determinantEqual_le_scalarDiagonal (heq ▸ inf_le_left)
  · exact not_determinantEqual_le_scalarDiagonal (top_unique (heq ▸ inf_le_left) ▸ le_top)

/-- **Over an algebraically closed field `K`, every pair in `GL ι K × GL ι K` factors as
`scalarDiagonal` times `determinantEqual`.** -/
theorem exists_mem_scalarDiagonal_mul_mem_determinantEqual {K : Type*} [Field K] [IsAlgClosed K]
    (p : GL ι K × GL ι K) :
    ∃ q ∈ scalarDiagonal ι K, ∃ r ∈ determinantEqual ι K, p = q * r := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact ⟨1, one_mem _, 1, one_mem _, Subsingleton.elim _ _⟩
  let d : Kˣ := p.1.det / p.2.det
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (d : K) (Fintype.card_pos (α := ι))
  have hc0 : c ≠ 0 := fun h0 => d.ne_zero (by rw [← hc, h0, zero_pow (Fintype.card_ne_zero)])
  let u : Kˣ := Units.mk0 c hc0
  have hu : u ^ Fintype.card ι = d := Units.ext (by simpa [u] using hc)
  refine ⟨(GeneralLinearGroup.scalar ι u, 1), mem_scalarDiagonal_iff.mpr ⟨u, by simp⟩,
    ((GeneralLinearGroup.scalar ι u)⁻¹ * p.1, p.2), ?_,
    Prod.ext (mul_inv_cancel_left _ p.1).symm (one_mul p.2).symm⟩
  rw [mem_determinantEqual_iff, map_mul, map_inv, GeneralLinearGroup.det_scalar, hu]
  simp only [d, inv_div, div_mul_cancel]

/-- Over an algebraically closed field `K`, `scalarDiagonal ι K` and `determinantEqual ι K`
generate `⊤`. -/
@[simp] theorem scalarDiagonal_sup_determinantEqual {K : Type*} [Field K] [IsAlgClosed K] :
    scalarDiagonal ι K ⊔ determinantEqual ι K = ⊤ :=
  eq_top_iff.mpr fun p _ =>
    let ⟨_, hq, _, hr, hp⟩ := exists_mem_scalarDiagonal_mul_mem_determinantEqual p
    hp ▸ Subgroup.mul_mem_sup hq hr

/-- **The unit-modulus determinant-ratio subgroup**
`{(g, h) | ‖(determinantRatio ι ℂ (g, h) : ℂ)‖ = 1}`. For `[Nonempty ι]`, this is a closed,
path-connected subgroup containing `diagonal ι ℂ` that strictly contains `determinantEqual ι ℂ` and
is not one of the four models in
`eq_diagonal_or_eq_scalarDiagonal_or_eq_determinantEqual_or_eq_top`, because it fails the
complex-closure hypothesis (`not_forall_pairExp_complex_smul_mem_determinantModulusOne`). -/
def determinantModulusOne (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Subgroup (GL ι ℂ × GL ι ℂ) where
  carrier := {p | ‖(determinantRatio ι ℂ p : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' {p q} hp hq := by
    simp only [Set.mem_ofPred_eq] at hp hq ⊢
    rw [map_mul, Units.val_mul, norm_mul, hp, hq, mul_one]
  inv_mem' {p} hp := by
    simp only [Set.mem_ofPred_eq] at hp ⊢
    rw [map_inv, Units.val_inv_eq_inv_val, norm_inv, hp, inv_one]

@[simp] theorem mem_determinantModulusOne_iff {p : GL ι ℂ × GL ι ℂ} :
    p ∈ determinantModulusOne ι ↔ ‖(determinantRatio ι ℂ p : ℂ)‖ = 1 := by rfl

/-- `determinantEqual ι ℂ` is contained in `determinantModulusOne ι`. -/
theorem determinantEqual_le_determinantModulusOne :
    determinantEqual ι ℂ ≤ determinantModulusOne ι := fun _ hp => by
  simp [mem_determinantEqual_iff.mp hp]

theorem graph_id_le_determinantModulusOne :
    (MonoidHom.id (GL ι ℂ)).graph ≤ determinantModulusOne ι :=
  graph_id_le_determinantEqual.trans determinantEqual_le_determinantModulusOne

/-- `determinantModulusOne ι` is closed in `GL ι ℂ × GL ι ℂ`. -/
theorem isClosed_determinantModulusOne :
    IsClosed (determinantModulusOne ι : Set (GL ι ℂ × GL ι ℂ)) := by
  rw [Subgroup.isClosed_iff_isClosed_goursatFst graph_id_le_determinantModulusOne,
    show ((determinantModulusOne ι).goursatFst : Set (GL ι ℂ)) =
      {g : GL ι ℂ | ‖(g : Matrix ι ι ℂ).det‖ = 1} from
      Set.ext fun g => by simp [Subgroup.mem_goursatFst, GeneralLinearGroup.val_det_apply]]
  exact isClosed_eq (continuous_norm.comp Units.continuous_val.matrix_det) continuous_const

/-- `determinantModulusOne ι` is path connected. -/
instance instPathConnectedSpaceDeterminantModulusOne :
    PathConnectedSpace (determinantModulusOne ι) := by
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i₀⟩⟩
  · rw [top_unique ((determinantEqual_eq_top_of_isEmpty (ι := ι) (R := ℂ)).ge.trans
      determinantEqual_le_determinantModulusOne)]
    exact isPathConnected_iff_pathConnectedSpace.mp
      (Subgroup.coe_top (G := GL ι ℂ × GL ι ℂ) ▸ isPathConnected_univ)
  rw [Subgroup.pathConnectedSpace_iff_pathConnectedSpace_goursatFst
    graph_id_le_determinantModulusOne]
  let expCircle : ℝ → ℂˣ := fun θ =>
    Units.mk0 (Complex.exp (θ * Complex.I)) (Complex.exp_ne_zero _)
  have hexp_cont : Continuous expCircle := Units.continuous_iff.mpr
    ⟨Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const),
     by simpa [expCircle, Function.comp_def, ← Complex.exp_neg] using
       Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const).neg⟩
  let param : SpecialLinearGroup ι ℂ × ℝ → (determinantModulusOne ι).goursatFst := fun p =>
    ⟨diagGL (Pi.mulSingle i₀ (expCircle p.2)) * SpecialLinearGroup.toGL p.1, by
      simp [expCircle, Subgroup.mem_goursatFst, Complex.norm_exp_ofReal_mul_I]⟩
  refine Function.Surjective.pathConnectedSpace (f := param) (fun ⟨g, hg⟩ => ?_)
    ((((continuous_diagGL.comp (continuous_mulSingle i₀)).comp
      (hexp_cont.comp continuous_snd)).mul
      (SpecialLinearGroup.isClosedEmbedding_toGL.continuous.comp continuous_fst)).subtype_mk _)
  have hgnorm : ‖(g : Matrix ι ι ℂ).det‖ = 1 := by
    simpa [Subgroup.mem_goursatFst, GeneralLinearGroup.val_det_apply] using hg
  let θ := Complex.arg (g : Matrix ι ι ℂ).det
  have hexp : (diagGL (Pi.mulSingle i₀ (expCircle θ))).det = g.det := Units.ext <| by
    rw [det_diagGL, Fintype.prod_pi_mulSingle']
    simpa [expCircle, GeneralLinearGroup.val_det_apply, hgnorm] using
      Complex.norm_mul_exp_arg_mul_I (g : Matrix ι ι ℂ).det
  let s : SpecialLinearGroup ι ℂ := ⟨((diagGL (Pi.mulSingle i₀ (expCircle θ)))⁻¹ * g : GL ι ℂ), by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, map_inv, hexp, inv_mul_cancel,
      Units.val_one]⟩
  refine ⟨(s, θ), Subtype.ext ?_⟩
  simp only [param]
  exact Units.ext (by
    rw [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix]
    simp only [s, ← Units.val_mul, mul_inv_cancel_left])

/-- For nonempty `ι`, `determinantEqual ι ℂ` is strictly contained in `determinantModulusOne ι`. -/
theorem determinantEqual_lt_determinantModulusOne [Nonempty ι] :
    determinantEqual ι ℂ < determinantModulusOne ι := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine lt_of_le_of_ne determinantEqual_le_determinantModulusOne fun heq => ?_
  let u : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  have hmem : (diagGL (Pi.mulSingle i₀ u), (1 : GL ι ℂ)) ∈ determinantModulusOne ι := by
    simp [u, mem_determinantModulusOne_iff]
  rw [← heq, mem_determinantEqual_iff, det_diagGL, Fintype.prod_pi_mulSingle',
    Units.ext_iff] at hmem
  simpa [u] using congrArg Complex.im hmem

/-- **`determinantModulusOne ι` fails complex closure** for nonempty `ι`. -/
theorem not_forall_pairExp_complex_smul_mem_determinantModulusOne [Nonempty ι] :
    ¬ (∀ X ∈ realDirections (determinantModulusOne ι), ∀ z : ℂ,
      pairExp (z • X) ∈ determinantModulusOne ι) := fun hcomplex => by
  have hnorm (z : ℂ) :
      ‖(NormedSpace.exp (z • (1 : Matrix ι ι ℂ))).det‖ = Real.exp (z.re * Fintype.card ι) := by
    rw [Matrix.det_exp, Matrix.trace_smul, Matrix.trace_one, ← Complex.exp_eq_exp_ℂ,
      smul_eq_mul, Complex.norm_exp]; simp
  let X : Matrix ι ι ℂ × Matrix ι ι ℂ := (Complex.I • 1, 0)
  have hX : X ∈ realDirections (determinantModulusOne ι) := mem_realDirections_iff.mpr fun t => by
    have ht : t • (Complex.I • (1 : Matrix ι ι ℂ)) = ((t : ℂ) * Complex.I) • 1 := by
      rw [← algebraMap_smul ℂ t, smul_smul, Complex.coe_algebraMap]
    simp [X, ht, GeneralLinearGroup.val_det_apply, hnorm]
  have hbad := hcomplex X hX Complex.I
  have hI : ‖(NormedSpace.exp (-1 : Matrix ι ι ℂ)).det‖ = Real.exp (-(Fintype.card ι : ℝ)) := by
    simpa using hnorm (-1)
  simp [X, GeneralLinearGroup.val_det_apply, smul_smul, hI, Fintype.card_ne_zero] at hbad

end TauCeti.DiagonalOvergroups
