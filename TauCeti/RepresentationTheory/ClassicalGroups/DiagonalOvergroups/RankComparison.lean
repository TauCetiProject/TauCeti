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
import TauCeti.Topology.Algebra.Group.Goursat

/-!
# Rank phenomena and real counterexample for diagonal overgroups of `GL ι ℂ`

This file complements the four-case classification in
`TauCeti.RepresentationTheory.ClassicalGroups.DiagonalOvergroups.Classification` by recording how
the four subgroups behave across ranks and why both connectedness and complex closure are
necessary hypotheses:

* **Rank `0` (`[IsEmpty ι]`):** `diagonal ι R = scalarDiagonal ι R = determinantEqual ι R = ⊤`.
* **Rank `1` (`[Unique ι]`):** `determinantEqual ι R = diagonal ι R` and `scalarDiagonal ι R = ⊤`.
* **Rank `≥ 2` (`[Nontrivial ι]` over `ℂ`):** all four subgroups are distinct; `scalarDiagonal ι ℂ`
  and `determinantEqual ι ℂ` are incomparable; their join is `⊤`; and their intersection consists of
  pairs differing by an `|ι|`-th root of unity scalar and is **not** connected (its non-identity
  components are witnessed by primitive `|ι|`-th roots of unity).
* **Real counterexample (`determinantModulusOne ι`):** the subgroup `{(g, h) | ‖det g / det h‖ = 1}`
  is closed and path-connected, strictly contains `determinantEqual ι ℂ` whenever `Nonempty ι`, and
  fails complex closure of `realDirections`.

## Main definitions

* `TauCeti.DiagonalOvergroups.determinantModulusOne`: pairs in `GL ι ℂ × GL ι ℂ` whose determinant
  ratio lies on the unit circle.

## Main results

* `TauCeti.DiagonalOvergroups.determinantEqual_eq_diagonal_of_unique`,
  `TauCeti.DiagonalOvergroups.scalarDiagonal_eq_top_of_unique`: the rank-`1` collapses.
* `TauCeti.DiagonalOvergroups.not_scalarDiagonal_le_determinantEqual`,
  `TauCeti.DiagonalOvergroups.not_determinantEqual_le_scalarDiagonal`:
  incomparability in rank `≥ 2`.
* `TauCeti.DiagonalOvergroups.not_isPreconnected_scalarDiagonal_inf_determinantEqual`:
  disconnectedness of `scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ` for `|ι| ≥ 2`.
* `TauCeti.DiagonalOvergroups.scalarDiagonal_sup_determinantEqual`: the join is `⊤`.
* `TauCeti.DiagonalOvergroups.determinantEqual_lt_determinantModulusOne`,
  `TauCeti.DiagonalOvergroups.not_forall_pairExp_complex_smul_mem_determinantModulusOne`:
  necessity of complex closure in `connected_complex_overgroup`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Springer GTM 222,
  2015, Chapters 1–3.
-/

public section

open Matrix NormedSpace

namespace TauCeti.DiagonalOvergroups

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-! ### Rank `0` and rank `1` collapses -/

@[simp]
theorem diagonal_eq_top_of_isEmpty [IsEmpty ι] : diagonal ι R = ⊤ :=
  eq_top_iff.mpr fun p _ => mem_diagonal_iff.mpr (Subsingleton.elim p.1 p.2)

@[simp]
theorem scalarDiagonal_eq_top_of_isEmpty [IsEmpty ι] : scalarDiagonal ι R = ⊤ :=
  top_unique (diagonal_eq_top_of_isEmpty (ι := ι) (R := R) ▸ diagonal_le_scalarDiagonal)

@[simp]
theorem determinantEqual_eq_top_of_isEmpty [IsEmpty ι] : determinantEqual ι R = ⊤ :=
  top_unique (diagonal_eq_top_of_isEmpty (ι := ι) (R := R) ▸ diagonal_le_determinantEqual)

@[simp]
theorem determinantEqual_eq_diagonal_of_unique [Unique ι] :
    determinantEqual ι R = diagonal ι R := by
  refine le_antisymm (fun p hp => mem_diagonal_iff.mpr ?_) diagonal_le_determinantEqual
  have hdet := congrArg Units.val (mem_determinantEqual_iff.mp hp)
  simp only [GeneralLinearGroup.val_det_apply, Matrix.det_unique] at hdet
  exact Units.ext (Matrix.ext fun i j => by
    rw [Unique.eq_default i, Unique.eq_default j]
    exact hdet)

@[simp]
theorem scalarDiagonal_eq_top_of_unique [Unique ι] : scalarDiagonal ι R = ⊤ := by
  refine eq_top_iff.mpr fun p _ => mem_scalarDiagonal_iff.mpr ⟨(p.1 / p.2).det, ?_⟩
  have hsc : GeneralLinearGroup.scalar ι (p.1 / p.2).det = p.1 / p.2 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [Unique.eq_default i, Unique.eq_default j, GeneralLinearGroup.coe_scalar,
      GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    simp
  rw [hsc, div_mul_cancel]

/-! ### Strictness, intersection, and join in rank `≥ 2` -/

/-- Membership in `scalarDiagonal ι R ⊓ determinantEqual ι R`: pairs differing by an `|ι|`-th root
of unity scalar. -/
theorem mem_scalarDiagonal_inf_determinantEqual_iff {p : GL ι R × GL ι R} :
    p ∈ scalarDiagonal ι R ⊓ determinantEqual ι R ↔
      ∃ u : Rˣ, u ^ Fintype.card ι = 1 ∧ p.1 = GeneralLinearGroup.scalar ι u * p.2 := by
  rw [Subgroup.mem_inf, mem_scalarDiagonal_iff, mem_determinantEqual_iff]
  constructor
  · rintro ⟨⟨u, hu⟩, hdet⟩
    refine ⟨u, ?_, hu⟩
    rw [hu, map_mul, GeneralLinearGroup.det_scalar] at hdet
    exact mul_right_cancel (hdet.trans (one_mul p.2.det).symm)
  · rintro ⟨u, hu1, hu⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [hu, map_mul, GeneralLinearGroup.det_scalar, hu1, one_mul]

/-- Over `ℂ`, `scalarDiagonal ι ℂ` and `determinantEqual ι ℂ` are incomparable when `|ι| ≥ 2`. -/
theorem not_scalarDiagonal_le_determinantEqual [Nontrivial ι] :
    ¬ (scalarDiagonal ι ℂ ≤ determinantEqual ι ℂ) := by
  intro hle
  let u : ℂˣ := Units.mk0 2 two_ne_zero
  have hmem : (GeneralLinearGroup.scalar ι u, (1 : GL ι ℂ)) ∈ determinantEqual ι ℂ :=
    hle (mem_scalarDiagonal_iff.mpr ⟨u, by simp⟩)
  have hdet := congrArg (fun x : ℂˣ => ‖(x : ℂ)‖) (mem_determinantEqual_iff.mp hmem)
  simp only [map_one, GeneralLinearGroup.det_scalar, Units.val_pow_eq_pow_val, Units.val_one,
    norm_pow, norm_one] at hdet
  have hu : ‖(u : ℂ)‖ = 2 := by simp [u]
  rw [hu] at hdet
  have hgt : (1 : ℝ) < 2 ^ Fintype.card ι :=
    one_lt_pow₀ (by norm_num) (Fintype.card_pos.ne')
  exact hgt.ne' hdet

theorem not_determinantEqual_le_scalarDiagonal [Nontrivial ι] [Nontrivial R] :
    ¬ (determinantEqual ι R ≤ scalarDiagonal ι R) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  intro hle
  let t := SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : R))
  have ht : (t, (1 : GL ι R)) ∈ determinantEqual ι R := by
    simp [t, mem_determinantEqual_iff]
  obtain ⟨u, hu⟩ := mem_scalarDiagonal_iff.mp (hle ht)
  have hij_eq := congrArg (fun M : Matrix ι ι R => M i j) (congrArg Units.val hu)
  simp [t, SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.transvection_coe,
    GeneralLinearGroup.coe_scalar, hij] at hij_eq

theorem diagonal_lt_scalarDiagonal [Nonempty ι] :
    diagonal ι ℂ < scalarDiagonal ι ℂ := by
  refine lt_of_le_of_ne diagonal_le_scalarDiagonal fun h => ?_
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let u : ℂˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  have hmem : (GeneralLinearGroup.scalar ι u, (1 : GL ι ℂ)) ∈ diagonal ι ℂ :=
    h ▸ mem_scalarDiagonal_iff.mpr ⟨u, by simp⟩
  have heq := congrArg (fun M : Matrix ι ι ℂ => M i₀ i₀)
    (congrArg Units.val (mem_diagonal_iff.mp hmem))
  norm_num [u, GeneralLinearGroup.coe_scalar] at heq

theorem diagonal_lt_determinantEqual [Nontrivial ι] [Nontrivial R] :
    diagonal ι R < determinantEqual ι R :=
  lt_of_le_of_ne diagonal_le_determinantEqual fun h =>
    not_determinantEqual_le_scalarDiagonal (h ▸ diagonal_le_scalarDiagonal)

theorem determinantEqual_lt_top [Nonempty ι] :
    determinantEqual ι ℂ < ⊤ := by
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  let u : ℂˣ := Units.mk0 2 two_ne_zero
  obtain ⟨g, hg⟩ := GeneralLinearGroup.det_surjective (n := ι) u
  have hmem : (g, (1 : GL ι ℂ)) ∈ determinantEqual ι ℂ := htop ▸ Subgroup.mem_top _
  have hdet := congrArg Units.val (mem_determinantEqual_iff.mp hmem)
  rw [hg, map_one] at hdet
  norm_num [u] at hdet

theorem scalarDiagonal_lt_top [Nontrivial ι] [Nontrivial R] :
    scalarDiagonal ι R < ⊤ :=
  lt_top_iff_ne_top.mpr scalarDiagonal_ne_top

/-- **For `|ι| ≥ 2`, the intersection `scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ` is not
connected**: a primitive `|ι|`-th root of unity lies in a non-identity component. -/
theorem not_isPreconnected_scalarDiagonal_inf_determinantEqual [Nontrivial ι] :
    ¬ IsPreconnected ((scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ :
      Subgroup (GL ι ℂ × GL ι ℂ)) : Set (GL ι ℂ × GL ι ℂ)) := by
  intro hconn
  have hc : IsClosed ((scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ :
      Subgroup (GL ι ℂ × GL ι ℂ)) : Set (GL ι ℂ × GL ι ℂ)) :=
    isClosed_scalarDiagonal.inter isClosed_determinantEqual
  have hd : diagonal ι ℂ ≤ scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ :=
    le_inf diagonal_le_scalarDiagonal diagonal_le_determinantEqual
  have hcomplex : ∀ X ∈ realDirections (scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ),
      ∀ z : ℂ, pairExp (z • X) ∈ scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ := by
    intro X hX z
    have hX1 : X ∈ scalarDiagonalLie ℂ ι := by
      rw [← SetLike.mem_coe, ← realDirections_scalarDiagonal]
      exact realDirections_mono inf_le_left hX
    have hX2 : X ∈ traceEqualLie ℂ ι := by
      rw [← SetLike.mem_coe, ← realDirections_determinantEqual]
      exact realDirections_mono inf_le_right hX
    have hz1 : z • X ∈ realDirections (scalarDiagonal ι ℂ) := by
      rw [realDirections_scalarDiagonal]
      exact (scalarDiagonalLie ℂ ι).smul_mem z hX1
    have hz2 : z • X ∈ realDirections (determinantEqual ι ℂ) := by
      rw [realDirections_determinantEqual]
      exact (traceEqualLie ℂ ι).smul_mem z hX2
    exact ⟨by simpa using mem_realDirections_iff.mp hz1 1,
      by simpa using mem_realDirections_iff.mp hz2 1⟩
  rcases connected_complex_overgroup _ hd hc hconn hcomplex with heq | heq | heq | heq
  · have : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ (Fintype.card ι)
    let u : ℂˣ := (hζ.isUnit (NeZero.ne _)).unit
    have hu : IsPrimitiveRoot u (Fintype.card ι) := IsPrimitiveRoot.coe_units_iff.mp hζ
    have hmem : (GeneralLinearGroup.scalar ι u, (1 : GL ι ℂ)) ∈
        scalarDiagonal ι ℂ ⊓ determinantEqual ι ℂ :=
      mem_scalarDiagonal_inf_determinantEqual_iff.mpr ⟨u, hu.pow_eq_one, by simp⟩
    rw [heq, mem_diagonal_iff] at hmem
    obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
    have hu1 : u = 1 := Units.ext <| by
      simpa [GeneralLinearGroup.coe_scalar] using
        congrArg (fun M : Matrix ι ι ℂ => M i₀ i₀) (congrArg Units.val hmem)
    exact hu.ne_one Fintype.one_lt_card hu1
  · exact not_scalarDiagonal_le_determinantEqual (heq ▸ inf_le_right)
  · exact not_determinantEqual_le_scalarDiagonal (heq ▸ inf_le_left)
  · exact not_determinantEqual_le_scalarDiagonal (top_unique (heq ▸ inf_le_left) ▸ le_top)

/-- **Every pair in `GL ι ℂ × GL ι ℂ` factors as an element of `scalarDiagonal ι ℂ` times an
element of `determinantEqual ι ℂ`.** -/
theorem exists_mem_scalarDiagonal_mul_mem_determinantEqual (p : GL ι ℂ × GL ι ℂ) :
    ∃ q ∈ scalarDiagonal ι ℂ, ∃ r ∈ determinantEqual ι ℂ, p = q * r := by
  rcases isEmpty_or_nonempty ι with h0 | hne
  · exact ⟨1, one_mem _, 1, one_mem _, Subsingleton.elim _ _⟩
  let d : ℂˣ := p.1.det / p.2.det
  let u : ℂˣ := Units.mk0 (Complex.exp (Complex.log (d : ℂ) / Fintype.card ι))
    (Complex.exp_ne_zero _)
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hu : u ^ Fintype.card ι = d := Units.ext <| by
    simp only [u, Units.val_pow_eq_pow_val, Units.val_mk0, ← Complex.exp_nat_mul]
    rw [mul_div_cancel₀ _ hcard, Complex.exp_log d.ne_zero]
  refine ⟨(GeneralLinearGroup.scalar ι u, 1), mem_scalarDiagonal_iff.mpr ⟨u, by simp⟩,
    ((GeneralLinearGroup.scalar ι u)⁻¹ * p.1, p.2), ?_, ?_⟩
  · rw [mem_determinantEqual_iff, map_mul, map_inv, GeneralLinearGroup.det_scalar, hu]
    change (p.1.det / p.2.det)⁻¹ * p.1.det = p.2.det
    rw [inv_div, div_mul_cancel]
  · exact Prod.ext (mul_inv_cancel_left _ p.1).symm (one_mul p.2).symm

/-- **The join `scalarDiagonal ι ℂ ⊔ determinantEqual ι ℂ` is the full product group.** -/
@[simp]
theorem scalarDiagonal_sup_determinantEqual :
    scalarDiagonal ι ℂ ⊔ determinantEqual ι ℂ = ⊤ := by
  refine eq_top_iff.mpr fun p _ => ?_
  obtain ⟨q, hq, r, hr, rfl⟩ := exists_mem_scalarDiagonal_mul_mem_determinantEqual p
  exact Subgroup.mul_mem_sup hq hr

/-! ### Real counterexample: modulus-one determinant ratio -/

/-- **Real Lie overgroup `r⁻¹(S¹)`**: pairs `(g, h) ∈ GL ι ℂ × GL ι ℂ` whose determinant ratio has
modulus `1`. For nonempty `ι` this subgroup is closed, path-connected, and contains
`determinantEqual ι ℂ` properly, showing that the complex-closure hypothesis in
`connected_complex_overgroup` cannot be omitted. -/
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

@[simp]
theorem mem_determinantModulusOne_iff {p : GL ι ℂ × GL ι ℂ} :
    p ∈ determinantModulusOne ι ↔ ‖(determinantRatio ι ℂ p : ℂ)‖ = 1 :=
  Iff.rfl

theorem determinantEqual_le_determinantModulusOne :
    determinantEqual ι ℂ ≤ determinantModulusOne ι := by
  intro p hp
  rw [mem_determinantModulusOne_iff, determinantRatio_apply, mem_determinantEqual_iff.mp hp,
    div_self', Units.val_one, norm_one]

theorem isClosed_determinantModulusOne :
    IsClosed (determinantModulusOne ι : Set (GL ι ℂ × GL ι ℂ)) := by
  have hd : (MonoidHom.id (GL ι ℂ)).graph ≤ determinantModulusOne ι :=
    diagonal_eq_graph_id (ι := ι) (R := ℂ) ▸
      diagonal_le_determinantEqual.trans determinantEqual_le_determinantModulusOne
  rw [Subgroup.isClosed_iff_isClosed_goursatFst hd]
  have hset : ((determinantModulusOne ι).goursatFst : Set (GL ι ℂ)) =
      {g : GL ι ℂ | ‖(g : Matrix ι ι ℂ).det‖ = 1} := by
    ext g
    simp [Subgroup.mem_goursatFst, GeneralLinearGroup.val_det_apply]
  rw [hset]
  exact isClosed_eq (continuous_norm.comp Units.continuous_val.matrix_det) continuous_const

private noncomputable def circleDiag (i₀ : ι) (θ : ℝ) : GL ι ℂ where
  val := Matrix.diagonal (Function.update (fun _ => (1 : ℂ)) i₀ (Complex.exp (θ * Complex.I)))
  inv := Matrix.diagonal (Function.update (fun _ => (1 : ℂ)) i₀ (Complex.exp (-(θ * Complex.I))))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    by_cases hi : i = i₀
    · subst hi; simp [← Complex.exp_add]
    · simp [hi]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    by_cases hi : i = i₀
    · subst hi; simp [← Complex.exp_add]
    · simp [hi]

private theorem continuous_circleDiag (i₀ : ι) : Continuous (circleDiag i₀) := by
  rw [Units.continuous_iff]
  refine ⟨(continuous_pi fun i => ?_).matrix_diagonal,
    (continuous_pi fun i => ?_).matrix_diagonal⟩
  · by_cases hi : i = i₀
    · subst hi
      change Continuous fun θ : ℝ =>
        Function.update (fun _ => (1 : ℂ)) i (Complex.exp (↑θ * Complex.I)) i
      simp only [Function.update_self]
      exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
    · change Continuous fun θ : ℝ =>
        Function.update (fun _ => (1 : ℂ)) i₀ (Complex.exp (↑θ * Complex.I)) i
      simp only [Function.update_of_ne hi]
      exact continuous_const
  · by_cases hi : i = i₀
    · subst hi
      change Continuous fun θ : ℝ =>
        Function.update (fun _ => (1 : ℂ)) i (Complex.exp (-(↑θ * Complex.I))) i
      simp only [Function.update_self]
      exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const).neg
    · change Continuous fun θ : ℝ =>
        Function.update (fun _ => (1 : ℂ)) i₀ (Complex.exp (-(↑θ * Complex.I))) i
      simp only [Function.update_of_ne hi]
      exact continuous_const

private theorem det_circleDiag (i₀ : ι) (θ : ℝ) :
    (circleDiag i₀ θ : Matrix ι ι ℂ).det = Complex.exp (θ * Complex.I) := by
  simp [circleDiag, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i₀)]

instance instPathConnectedSpaceDeterminantModulusOne :
    PathConnectedSpace (determinantModulusOne ι) := by
  have hd : (MonoidHom.id (GL ι ℂ)).graph ≤ determinantModulusOne ι :=
    diagonal_eq_graph_id (ι := ι) (R := ℂ) ▸
      diagonal_le_determinantEqual.trans determinantEqual_le_determinantModulusOne
  rw [Subgroup.pathConnectedSpace_iff_pathConnectedSpace_goursatFst hd]
  rcases isEmpty_or_nonempty ι with h0 | hne
  · exact ⟨⟨1⟩, fun x y => Subsingleton.elim x y ▸ Joined.refl x⟩
  obtain ⟨i₀⟩ := hne
  let param : SpecialLinearGroup ι ℂ × ℝ → (determinantModulusOne ι).goursatFst := fun p =>
    ⟨circleDiag i₀ p.2 * SpecialLinearGroup.toGL p.1, by
      simp [Subgroup.mem_goursatFst, GeneralLinearGroup.val_det_apply, det_circleDiag,
        Complex.norm_exp_ofReal_mul_I]⟩
  have hparam_cont : Continuous param :=
    (((continuous_circleDiag i₀).comp continuous_snd).mul
      (SpecialLinearGroup.isClosedEmbedding_toGL.continuous.comp continuous_fst)).subtype_mk _
  have hparam_surj : Function.Surjective param := by
    rintro ⟨g, hg⟩
    have hgnorm : ‖(g : Matrix ι ι ℂ).det‖ = 1 := by
      simpa [Subgroup.mem_goursatFst, GeneralLinearGroup.val_det_apply] using hg
    let θ := Complex.arg (g : Matrix ι ι ℂ).det
    have hexp : (circleDiag i₀ θ).det = g.det := Units.ext <| by
      rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_det_apply, det_circleDiag]
      have harg := Complex.norm_mul_exp_arg_mul_I (g : Matrix ι ι ℂ).det
      rwa [hgnorm, Complex.ofReal_one, one_mul] at harg
    let s : SpecialLinearGroup ι ℂ :=
      ⟨((circleDiag i₀ θ)⁻¹ * g : GL ι ℂ), by
        rw [← GeneralLinearGroup.val_det_apply, map_mul, map_inv, hexp, inv_mul_cancel,
          Units.val_one]⟩
    have hs : SpecialLinearGroup.toGL s = (circleDiag i₀ θ)⁻¹ * g :=
      Units.ext (SpecialLinearGroup.coe_GL_coe_matrix s)
    refine ⟨(s, θ), Subtype.ext ?_⟩
    change circleDiag i₀ θ * SpecialLinearGroup.toGL s = g
    rw [hs, mul_inv_cancel_left]
  exact hparam_surj.pathConnectedSpace hparam_cont

theorem determinantEqual_lt_determinantModulusOne [Nonempty ι] :
    determinantEqual ι ℂ < determinantModulusOne ι := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine lt_of_le_of_ne determinantEqual_le_determinantModulusOne fun heq => ?_
  let z : ℂ := (3 + 4 * Complex.I) / 5
  have hznorm : ‖z‖ = 1 := by
    rw [Complex.norm_def, Real.sqrt_eq_one]
    norm_num [z, Complex.normSq_apply]
  let g : GL ι ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal (Function.update (fun _ => (1 : ℂ)) i₀ z))
    (by
      rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i₀)]
      simp only [Finset.prod_const_one, mul_one]
      rw [← norm_ne_zero_iff, hznorm]
      exact one_ne_zero)
  have hgdet : (g : Matrix ι ι ℂ).det = z := by
    simp [g, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i₀)]
  have hmem : (g, (1 : GL ι ℂ)) ∈ determinantModulusOne ι := by
    simp [mem_determinantModulusOne_iff, GeneralLinearGroup.val_det_apply, hgdet, hznorm]
  rw [← heq, mem_determinantEqual_iff, Units.ext_iff] at hmem
  have hz1 : z = 1 := by
    simpa [GeneralLinearGroup.val_det_apply, hgdet] using hmem
  have him := congrArg Complex.im hz1
  norm_num [z] at him

/-- **`determinantModulusOne ι` fails complex closure** for nonempty `ι`: `(i • 1, 0)` is a real
direction, whereas multiplying by `i` produces `(-1, 0)`, whose determinant ratio at `t = 1` has
modulus `exp (-|ι|) ≠ 1`. -/
theorem not_forall_pairExp_complex_smul_mem_determinantModulusOne [Nonempty ι] :
    ¬ (∀ X ∈ realDirections (determinantModulusOne ι), ∀ z : ℂ,
      pairExp (z • X) ∈ determinantModulusOne ι) := by
  intro hcomplex
  let X : Matrix ι ι ℂ × Matrix ι ι ℂ := (Complex.I • 1, 0)
  have hX : X ∈ realDirections (determinantModulusOne ι) := by
    rw [mem_realDirections_iff]
    intro t
    rw [mem_determinantModulusOne_iff, determinantRatio_apply]
    have hdet2 : (pairExp (t • X)).2.det = 1 := by
      rw [Units.ext_iff]
      simp [X, GeneralLinearGroup.val_det_apply]
    rw [hdet2, div_one, GeneralLinearGroup.val_det_apply, coe_fst_pairExp, Prod.smul_fst,
      Matrix.det_exp, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one]
    have htr : t • (Complex.I • (Fintype.card ι : ℂ)) =
        ((t * Fintype.card ι : ℝ) : ℂ) * Complex.I := by
      simp [Complex.real_smul]
      ring
    rw [htr, ← Complex.exp_eq_exp_ℂ]
    exact Complex.norm_exp_ofReal_mul_I _
  have hbad := hcomplex X hX Complex.I
  rw [mem_determinantModulusOne_iff, determinantRatio_apply] at hbad
  have hdet2 : (pairExp (Complex.I • X)).2.det = 1 := by
    rw [Units.ext_iff]
    simp [X, GeneralLinearGroup.val_det_apply]
  rw [hdet2, div_one, GeneralLinearGroup.val_det_apply, coe_fst_pairExp, Prod.smul_fst,
    Matrix.det_exp] at hbad
  have htr : (Complex.I • (Complex.I • (1 : Matrix ι ι ℂ))).trace = -(Fintype.card ι : ℂ) := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, Matrix.trace_neg, Matrix.trace_one]
  rw [htr, ← Complex.exp_eq_exp_ℂ] at hbad
  have hnorm : ‖Complex.exp (-(Fintype.card ι : ℂ))‖ = Real.exp (-(Fintype.card ι : ℝ)) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [hnorm, Real.exp_eq_one_iff, neg_eq_zero, Nat.cast_eq_zero] at hbad
  exact Fintype.card_ne_zero hbad

end TauCeti.DiagonalOvergroups
