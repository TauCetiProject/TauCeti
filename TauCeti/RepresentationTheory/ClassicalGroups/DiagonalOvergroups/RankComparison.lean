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
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.Topology.Algebra.Group.Goursat

/-!
# Rank phenomena and real counterexample for diagonal overgroups of `GL ι ℂ`

Complements `TauCeti.RepresentationTheory.ClassicalGroups.DiagonalOvergroups.Classification` with:
* rank `0` (`[IsEmpty ι]`): all four subgroups equal `⊤`;
* rank `1` (`[Unique ι]`): `determinantEqual ι R = diagonal ι R` and `scalarDiagonal ι R = ⊤`;
* rank `≥ 2` (`[Nontrivial ι]` over `ℂ`): all four subgroups are distinct, `scalarDiagonal ι ℂ` and
  `determinantEqual ι ℂ` are incomparable with join `⊤` and disconnected intersection;
* the closed path-connected real Lie counterexample `determinantModulusOne ι`
  (`‖det g / det h‖ = 1`), strictly containing `determinantEqual ι ℂ` for `Nonempty ι`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222, 2015,
  Chapters 1–3.
-/

public section

open Matrix NormedSpace

namespace TauCeti.DiagonalOvergroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

@[simp] theorem diagonal_eq_top_of_isEmpty [IsEmpty ι] : diagonal ι R = ⊤ :=
  eq_top_iff.mpr fun p _ => mem_diagonal_iff.mpr (Subsingleton.elim p.1 p.2)

@[simp] theorem scalarDiagonal_eq_top_of_isEmpty [IsEmpty ι] : scalarDiagonal ι R = ⊤ :=
  top_unique (diagonal_eq_top_of_isEmpty (ι := ι) (R := R) ▸ diagonal_le_scalarDiagonal)

@[simp] theorem determinantEqual_eq_top_of_isEmpty [IsEmpty ι] : determinantEqual ι R = ⊤ :=
  top_unique (diagonal_eq_top_of_isEmpty (ι := ι) (R := R) ▸ diagonal_le_determinantEqual)

@[simp] theorem determinantEqual_eq_diagonal_of_unique [Unique ι] :
    determinantEqual ι R = diagonal ι R := by
  refine le_antisymm (fun p hp => mem_diagonal_iff.mpr ?_) diagonal_le_determinantEqual
  have hdet := congrArg Units.val (mem_determinantEqual_iff.mp hp)
  simp only [GeneralLinearGroup.val_det_apply, Matrix.det_unique] at hdet
  exact Units.ext (Matrix.ext fun i j => by
    rw [Unique.eq_default i, Unique.eq_default j]; exact hdet)

@[simp] theorem scalarDiagonal_eq_top_of_unique [Unique ι] : scalarDiagonal ι R = ⊤ := by
  refine eq_top_iff.mpr fun p _ => mem_scalarDiagonal_iff.mpr ⟨(p.1 / p.2).det, ?_⟩
  have hsc : GeneralLinearGroup.scalar ι (p.1 / p.2).det = p.1 / p.2 :=
    Units.ext (Matrix.ext fun i j => by
      rw [Unique.eq_default i, Unique.eq_default j, GeneralLinearGroup.coe_scalar,
        GeneralLinearGroup.val_det_apply, Matrix.det_unique]; simp)
  rw [hsc, div_mul_cancel]

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

theorem not_scalarDiagonal_le_determinantEqual [Nontrivial ι] :
    ¬ (scalarDiagonal ι ℂ ≤ determinantEqual ι ℂ) := fun hle => by
  let u : ℂˣ := Units.mk0 2 two_ne_zero
  have hdet := congrArg (fun x : ℂˣ => ‖(x : ℂ)‖) (mem_determinantEqual_iff.mp
    (hle ((mem_scalarDiagonal_iff (p := (GeneralLinearGroup.scalar ι u, 1))).mpr
      ⟨u, (mul_one _).symm⟩)))
  simp only [u, map_one, GeneralLinearGroup.det_scalar, Units.val_pow_eq_pow_val, Units.val_one,
    Units.val_mk0, norm_pow, Complex.norm_ofNat, norm_one] at hdet
  exact (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) Fintype.card_pos.ne').ne' hdet

theorem not_determinantEqual_le_scalarDiagonal [Nontrivial ι] [Nontrivial R] :
    ¬ (determinantEqual ι R ≤ scalarDiagonal ι R) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  intro hle
  obtain ⟨u, hu⟩ := mem_scalarDiagonal_iff.mp (hle ((mem_determinantEqual_iff
    (p := (SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : R)), 1))).mpr
    (by simp)))
  simpa [SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.transvection_coe,
    GeneralLinearGroup.coe_scalar, hij] using
    congrArg (fun M : Matrix ι ι R => M i j) (congrArg Units.val hu)

theorem diagonal_lt_scalarDiagonal [Nonempty ι] : diagonal ι ℂ < scalarDiagonal ι ℂ := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine lt_of_le_of_ne diagonal_le_scalarDiagonal fun h => ?_
  let u : ℂˣ := Units.mk0 (-1) (by norm_num)
  have heq := congrArg (fun M : Matrix ι ι ℂ => M i₀ i₀) (congrArg Units.val (mem_diagonal_iff.mp
    (h ▸ (mem_scalarDiagonal_iff (p := (GeneralLinearGroup.scalar ι u, 1))).mpr
      ⟨u, (mul_one _).symm⟩)))
  norm_num [u, GeneralLinearGroup.coe_scalar] at heq

theorem diagonal_lt_determinantEqual [Nontrivial ι] [Nontrivial R] :
    diagonal ι R < determinantEqual ι R :=
  lt_of_le_of_ne diagonal_le_determinantEqual fun h =>
    not_determinantEqual_le_scalarDiagonal (h ▸ diagonal_le_scalarDiagonal)

theorem determinantEqual_lt_top [Nonempty ι] : determinantEqual ι ℂ < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  obtain ⟨g, hg⟩ := GeneralLinearGroup.det_surjective (n := ι) (Units.mk0 (2 : ℂ) two_ne_zero)
  have hdet := congrArg Units.val (mem_determinantEqual_iff.mp (htop ▸ Subgroup.mem_top (g, 1)))
  norm_num [hg] at hdet

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
  rcases connected_complex_overgroup _ (le_inf diagonal_le_scalarDiagonal
      diagonal_le_determinantEqual) (isClosed_scalarDiagonal.inter isClosed_determinantEqual)
      hconn hcomplex with heq | heq | heq | heq
  · have : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ (Fintype.card ι)
    let u : ℂˣ := (hζ.isUnit (NeZero.ne _)).unit
    have hu : IsPrimitiveRoot u (Fintype.card ι) := IsPrimitiveRoot.coe_units_iff.mp hζ
    have hmem : (GeneralLinearGroup.scalar ι u, (1 : GL ι ℂ)) ∈ diagonal ι ℂ :=
      heq ▸ mem_scalarDiagonal_inf_determinantEqual_iff.mpr ⟨u, hu.pow_eq_one, by simp⟩
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    exact hu.ne_one Fintype.one_lt_card (Units.ext <| by
      simpa [GeneralLinearGroup.coe_scalar] using
        congrArg (fun M : Matrix ι ι ℂ => M i₀ i₀) (congrArg Units.val (mem_diagonal_iff.mp hmem)))
  · exact not_scalarDiagonal_le_determinantEqual (heq ▸ inf_le_right)
  · exact not_determinantEqual_le_scalarDiagonal (heq ▸ inf_le_left)
  · exact not_determinantEqual_le_scalarDiagonal (top_unique (heq ▸ inf_le_left) ▸ le_top)

/-- **Every pair in `GL ι ℂ × GL ι ℂ` factors as `scalarDiagonal` times `determinantEqual`.** -/
theorem exists_mem_scalarDiagonal_mul_mem_determinantEqual (p : GL ι ℂ × GL ι ℂ) :
    ∃ q ∈ scalarDiagonal ι ℂ, ∃ r ∈ determinantEqual ι ℂ, p = q * r := by
  rcases isEmpty_or_nonempty ι with _ | _
  · exact ⟨1, one_mem _, 1, one_mem _, Subsingleton.elim _ _⟩
  let d : ℂˣ := p.1.det / p.2.det
  let u : ℂˣ := Units.mk0 (Complex.exp (Complex.log (d : ℂ) / Fintype.card ι))
    (Complex.exp_ne_zero _)
  have hu : u ^ Fintype.card ι = d := Units.ext <| by
    simp only [u, Units.val_pow_eq_pow_val, Units.val_mk0, ← Complex.exp_nat_mul]
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), Complex.exp_log d.ne_zero]
  refine ⟨(GeneralLinearGroup.scalar ι u, 1), mem_scalarDiagonal_iff.mpr ⟨u, by simp⟩,
    ((GeneralLinearGroup.scalar ι u)⁻¹ * p.1, p.2), ?_,
    Prod.ext (mul_inv_cancel_left _ p.1).symm (one_mul p.2).symm⟩
  rw [mem_determinantEqual_iff, map_mul, map_inv, GeneralLinearGroup.det_scalar, hu]
  change (p.1.det / p.2.det)⁻¹ * p.1.det = p.2.det; rw [inv_div, div_mul_cancel]

@[simp] theorem scalarDiagonal_sup_determinantEqual :
    scalarDiagonal ι ℂ ⊔ determinantEqual ι ℂ = ⊤ :=
  eq_top_iff.mpr fun p _ =>
    let ⟨_, hq, _, hr, hp⟩ := exists_mem_scalarDiagonal_mul_mem_determinantEqual p
    hp ▸ Subgroup.mul_mem_sup hq hr

/-- **Real Lie overgroup `r⁻¹(S¹)`**: pairs `(g, h)` whose determinant ratio has modulus `1`. -/
def determinantModulusOne (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Subgroup (GL ι ℂ × GL ι ℂ) where
  carrier := {p | ‖(determinantRatio ι ℂ p : ℂ)‖ = 1}
  one_mem' := by simp
  mul_mem' {p q} hp hq := by
    change ‖((determinantRatio ι ℂ (p * q) : ℂˣ) : ℂ)‖ = 1
    rw [map_mul, Units.val_mul, norm_mul, hp, hq, mul_one]
  inv_mem' {p} hp := by
    change ‖((determinantRatio ι ℂ p⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [map_inv, Units.val_inv_eq_inv_val, norm_inv, hp, inv_one]

@[simp] theorem mem_determinantModulusOne_iff {p : GL ι ℂ × GL ι ℂ} :
    p ∈ determinantModulusOne ι ↔ ‖(determinantRatio ι ℂ p : ℂ)‖ = 1 := by rfl

theorem determinantEqual_le_determinantModulusOne :
    determinantEqual ι ℂ ≤ determinantModulusOne ι := fun _ hp => by
  rw [mem_determinantModulusOne_iff, determinantRatio_apply, mem_determinantEqual_iff.mp hp,
    div_self', Units.val_one, norm_one]

theorem isClosed_determinantModulusOne :
    IsClosed (determinantModulusOne ι : Set (GL ι ℂ × GL ι ℂ)) := by
  rw [Subgroup.isClosed_iff_isClosed_goursatFst (diagonal_eq_graph_id (ι := ι) (R := ℂ) ▸
    diagonal_le_determinantEqual.trans determinantEqual_le_determinantModulusOne),
    show ((determinantModulusOne ι).goursatFst : Set (GL ι ℂ)) =
      {g : GL ι ℂ | ‖(g : Matrix ι ι ℂ).det‖ = 1} from
      Set.ext fun g => by simp [Subgroup.mem_goursatFst, GeneralLinearGroup.val_det_apply]]
  exact isClosed_eq (continuous_norm.comp Units.continuous_val.matrix_det) continuous_const

private theorem continuous_diagGL_mulSingle (i₀ : ι) :
    Continuous fun u : ℂˣ => diagGL (Pi.mulSingle i₀ u) :=
  (Units.continuous_iff.mpr
    ⟨by
      simpa only [Function.comp_def, diagGL_coe] using
        (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal,
     by
      simpa only [Function.comp_def, ← map_inv, diagGL_coe, Pi.inv_apply] using
        (continuous_pi fun i =>
          (Units.continuous_coe_inv (M := ℂ)).comp (continuous_apply i)).matrix_diagonal⟩).comp
    (continuous_mulSingle i₀)

instance instPathConnectedSpaceDeterminantModulusOne :
    PathConnectedSpace (determinantModulusOne ι) := by
  rw [Subgroup.pathConnectedSpace_iff_pathConnectedSpace_goursatFst
    (diagonal_eq_graph_id (ι := ι) (R := ℂ) ▸
      diagonal_le_determinantEqual.trans determinantEqual_le_determinantModulusOne)]
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i₀⟩⟩
  · exact ⟨⟨1⟩, fun x y => Subsingleton.elim x y ▸ Joined.refl x⟩
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
    ((((continuous_diagGL_mulSingle i₀).comp (hexp_cont.comp continuous_snd)).mul
      (SpecialLinearGroup.isClosedEmbedding_toGL.continuous.comp continuous_fst)).subtype_mk _)
  have hgnorm : ‖(g : Matrix ι ι ℂ).det‖ = 1 := by
    simpa [Subgroup.mem_goursatFst, GeneralLinearGroup.val_det_apply] using hg
  let θ := Complex.arg (g : Matrix ι ι ℂ).det
  have hexp : (diagGL (Pi.mulSingle i₀ (expCircle θ))).det = g.det := Units.ext <| by
    rw [det_diagGL, Fintype.prod_pi_mulSingle']
    simpa [expCircle, GeneralLinearGroup.val_det_apply, hgnorm] using
      Complex.norm_mul_exp_arg_mul_I (g : Matrix ι ι ℂ).det
  refine ⟨(⟨((diagGL (Pi.mulSingle i₀ (expCircle θ)))⁻¹ * g : GL ι ℂ), by
    rw [← GeneralLinearGroup.val_det_apply, map_mul, map_inv, hexp, inv_mul_cancel,
      Units.val_one]⟩, θ), Subtype.ext ?_⟩
  change diagGL (Pi.mulSingle i₀ (expCircle θ)) * _ = g
  rw [show SpecialLinearGroup.toGL _ = (diagGL (Pi.mulSingle i₀ (expCircle θ)))⁻¹ * g from
    Units.ext (SpecialLinearGroup.coe_GL_coe_matrix _), mul_inv_cancel_left]

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
  let X : Matrix ι ι ℂ × Matrix ι ι ℂ := (Complex.I • 1, 0)
  have hX : X ∈ realDirections (determinantModulusOne ι) := mem_realDirections_iff.mpr fun t => by
    have hdet2 : (pairExp (t • X)).2.det = 1 :=
      Units.ext (by simp [X, GeneralLinearGroup.val_det_apply])
    rw [mem_determinantModulusOne_iff, determinantRatio_apply, hdet2, div_one,
      GeneralLinearGroup.val_det_apply, coe_fst_pairExp, Prod.smul_fst, Matrix.det_exp,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, ← Complex.exp_eq_exp_ℂ]
    have htr : t • (Complex.I • (Fintype.card ι : ℂ)) =
        ((t * Fintype.card ι : ℝ) : ℂ) * Complex.I := by simp [Complex.real_smul]; ring
    rw [htr]; exact Complex.norm_exp_ofReal_mul_I _
  have hbad := hcomplex X hX Complex.I
  have hdet2 : (pairExp (Complex.I • X)).2.det = 1 :=
    Units.ext (by simp [X, GeneralLinearGroup.val_det_apply])
  rw [mem_determinantModulusOne_iff, determinantRatio_apply, hdet2, div_one,
    GeneralLinearGroup.val_det_apply, coe_fst_pairExp, Prod.smul_fst, Matrix.det_exp,
    show (Complex.I • (Complex.I • (1 : Matrix ι ι ℂ))).trace = -(Fintype.card ι : ℂ) by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul, Matrix.trace_neg, Matrix.trace_one],
    ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_eq_one_iff, neg_eq_zero,
    Nat.cast_eq_zero] at hbad
  exact Fintype.card_ne_zero hbad

end TauCeti.DiagonalOvergroups
