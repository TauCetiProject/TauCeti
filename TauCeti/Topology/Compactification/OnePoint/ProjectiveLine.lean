/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo

/-!
# Möbius transformations of the projective line

Mathlib's `OnePoint.smul_some_eq_ite` and `OnePoint.smul_infty_eq_ite` give the *value* of the
`GL (Fin 2) K` action on `OnePoint K`. This file adds the companion *criterion* for the
exceptional case — when an affine point is carried to `∞` — which Mathlib does not state.

It then equips `OnePoint K` with the action of the projective special linear group
`PSL(2, K)`, transported from Mathlib's action of `PSL(2, K)` on `ℙ K (Fin 2 → K)` along
`OnePoint.equivProjectivization`. The class of a matrix acts as the matrix does
(`OnePoint.pslMk_smul`); the action is faithful and transitive. For `K = ℝ` this is the action of
`PSL(2, ℝ)` on the ideal boundary of the upper half-plane.

When `K` has characteristic other than two (`[NeZero (2 : K)]`), a parabolic element `g` of
`PSL(2, K)` (`Matrix.ProjectiveSpecialLinearGroup.IsParabolic`) has exactly one fixed point,
`parabolicFixedPoint g`, the descent of Mathlib's
`Matrix.GeneralLinearGroup.parabolicFixedPoint`. A parabolic element fixing `∞` is a nonzero
translation, and so a parabolic element is conjugate to a translation by any `σ` carrying `∞` to
its fixed point. This normal form is where the cusps of a Fuchsian group are measured from: the
stabilizer of a cusp, moved to `∞`, consists of translations.

## Main results

* `OnePoint.smul_some_eq_infty_iff`: `g • (k : OnePoint K) = ∞` exactly when the denominator
  `g 1 0 * k + g 1 1` vanishes.
* `OnePoint.instMulActionPSL`: the action of `PSL(2, K)` on `OnePoint K`, with `pslMk_smul`.
* `Matrix.ProjectiveSpecialLinearGroup.IsParabolic.smul_eq_self_iff`: a parabolic element fixes
  a point exactly when it is `parabolicFixedPoint g` (in characteristic other than two).
* `Matrix.ProjectiveSpecialLinearGroup.isParabolic_iff_exists_eq_upperRightHom`: an element
  fixing `∞` is parabolic exactly when it is a nonzero translation.
* `Matrix.ProjectiveSpecialLinearGroup.exists_conj_upperRightHom_of_smul_infty`: conjugation by
  an element fixing `∞` rescales every translation by the same nonzero square, and
  `Matrix.ProjectiveSpecialLinearGroup.exists_eq_upperRightHom_of_commute`: such an element
  commuting with a nonzero translation is itself a translation.
* `Matrix.ProjectiveSpecialLinearGroup.IsParabolic.exists_conj_eq_upperRightHom` and
  `Matrix.ProjectiveSpecialLinearGroup.isParabolic_iff_exists_conj_upperRightHom`: the parabolic
  elements are exactly the conjugates of nonzero translations (in characteristic other than two).

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §4.3.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§2.1 and 4.2.
-/

public section

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace OnePoint

open Matrix

variable {K : Type*} [Field K] [DecidableEq K]

/-- **When a Möbius image is the point at infinity.** Mathlib's `smul_some_eq_ite` gives the
*value* of `g • (k : OnePoint K)`; this is the companion criterion for the exceptional case.

`[DecidableEq K]` is a hypothesis of the *statement*, not of the proof: Mathlib's `instGLAction`
is itself declared under `[Field K] [DecidableEq K]`
(`Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean`), so `g • (k : OnePoint K)` does
not elaborate without it. -/
@[simp]
lemma smul_some_eq_infty_iff {g : GL (Fin 2) K} {k : K} :
    g • (k : OnePoint K) = ∞ ↔ (g : Matrix (Fin 2) (Fin 2) K) 1 0 * k +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
  rw [smul_some_eq_ite]
  split_ifs with hz
  · simp [hz]
  · simp [hz]

/-- The projective special linear group `PSL(2, K)` acts on `OnePoint K`, via the canonical
identification with `ℙ¹(K)`. -/
noncomputable instance instMulActionPSL : MulAction PSL(2, K) (OnePoint K) :=
  (equivProjectivization K).mulAction PSL(2, K)

/-- The class in `PSL(2, K)` of a matrix of `SL(2, K)` acts on `OnePoint K` as the matrix does. -/
@[simp]
lemma pslMk_smul (g : SL(2, K)) (c : OnePoint K) :
    (g : PSL(2, K)) • c = (g : GL (Fin 2) K) • c :=
  (rfl)

/-- The action of `PSL(2, K)` on `OnePoint K` is faithful. -/
instance : FaithfulSMul PSL(2, K) (OnePoint K) where
  eq_of_smul_eq_smul {g₁ g₂} h := eq_of_smul_eq_smul fun p : ℙ K (Fin 2 → K) ↦ by
    simpa [Equiv.smul_def] using
      congrArg (equivProjectivization K) (h ((equivProjectivization K).symm p))

/-- The action of `PSL(2, K)` on `OnePoint K` is transitive. -/
instance : MulAction.IsPretransitive PSL(2, K) (OnePoint K) :=
  MulAction.IsPretransitive.of_surjective_map (M := PSL(2, K)) (α := ℙ K (Fin 2 → K))
    (f := ⟨(equivProjectivization K).symm, fun g p ↦ by
      rw [Equiv.smul_def (equivProjectivization K), Equiv.apply_symm_apply]⟩)
    (equivProjectivization K).symm.surjective inferInstance

end OnePoint

namespace Matrix.ProjectiveSpecialLinearGroup

open OnePoint

variable {K : Type*} [Field K] [DecidableEq K]

/-- The translation `upperRightHom x` fixes `∞`. -/
@[simp]
theorem upperRightHom_smul_infty (x : K) : upperRightHom x • (∞ : OnePoint K) = ∞ := by
  simp [upperRightHom_apply, smul_infty_eq_self_iff, SpecialLinearGroup.transvection_coe]

/-- The translation `upperRightHom x` acts on `K ⊆ OnePoint K` by `k ↦ k + x`. -/
@[simp]
theorem upperRightHom_smul_coe (x k : K) :
    upperRightHom x • (k : OnePoint K) = ((k + x : K) : OnePoint K) := by
  simp [upperRightHom_apply, smul_some_eq_ite, SpecialLinearGroup.transvection_coe]

/-- The fixed point of a parabolic element of `PSL(2, K)`, well defined because the formula
`Matrix.GeneralLinearGroup.parabolicFixedPoint` is unchanged by negating the representative. For a
parabolic `g` it is the unique fixed point of `g` (`IsParabolic.smul_eq_self_iff`); otherwise it
carries no meaning. -/
noncomputable def parabolicFixedPoint (g : PSL(2, K)) : OnePoint K :=
  Quotient.liftOn' g (fun a : SL(2, K) ↦ (a : GL (Fin 2) K).parabolicFixedPoint) fun a b hab ↦ by
    rw [QuotientGroup.leftRel_apply,
      SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at hab
    rcases hab with hab | hab
    · rw [inv_mul_eq_one.mp hab]
    · rw [inv_mul_eq_iff_eq_mul, mul_neg_one] at hab
      subst hab
      simp only [GeneralLinearGroup.parabolicFixedPoint]
      split_ifs <;> simp_all [neg_add_eq_sub, div_neg, ← neg_div]

@[simp]
theorem parabolicFixedPoint_mk (a : SL(2, K)) :
    parabolicFixedPoint (a : PSL(2, K)) = (a : GL (Fin 2) K).parabolicFixedPoint :=
  (rfl)

/-- The fixed point of a translation is `∞`. -/
@[simp]
theorem parabolicFixedPoint_upperRightHom (x : K) :
    parabolicFixedPoint (upperRightHom x) = ∞ := by
  simp [upperRightHom_apply, GeneralLinearGroup.parabolicFixedPoint,
    SpecialLinearGroup.transvection_coe]

/-- A parabolic element of `PSL(2, K)` fixes exactly one point of `OnePoint K`, namely
`parabolicFixedPoint g`. -/
theorem IsParabolic.smul_eq_self_iff [NeZero (2 : K)] {g : PSL(2, K)} (hg : IsParabolic g)
    {c : OnePoint K} : g • c = c ↔ c = parabolicFixedPoint g := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  rw [isParabolic_mk_iff] at hg
  rw [pslMk_smul, parabolicFixedPoint_mk, hg.smul_eq_self_iff]

theorem IsParabolic.smul_parabolicFixedPoint [NeZero (2 : K)] {g : PSL(2, K)}
    (hg : IsParabolic g) : g • parabolicFixedPoint g = parabolicFixedPoint g :=
  hg.smul_eq_self_iff.mpr rfl

/-- The fixed point of a conjugate `σ g σ⁻¹` of a parabolic element is the image under `σ` of the
fixed point of `g`. -/
theorem IsParabolic.parabolicFixedPoint_conj [NeZero (2 : K)] {g : PSL(2, K)}
    (hg : IsParabolic g) (σ : PSL(2, K)) :
    parabolicFixedPoint (σ * g * σ⁻¹) = σ • parabolicFixedPoint g := by
  refine (((isParabolic_conj_iff σ g).mpr hg).smul_eq_self_iff.mp ?_).symm
  rw [mul_smul, mul_smul, inv_smul_smul, hg.smul_parabolicFixedPoint]

/-- An element of `PSL(2, K)` fixing `∞` is parabolic exactly when it is a nonzero translation. -/
theorem isParabolic_iff_exists_eq_upperRightHom {g : PSL(2, K)}
    (hg : g • (∞ : OnePoint K) = ∞) : IsParabolic g ↔ ∃ x ≠ 0, g = upperRightHom x := by
  refine ⟨fun hpar ↦ ?_, fun ⟨x, hx, hgx⟩ ↦ hgx ▸ isParabolic_upperRightHom_iff.mpr hx⟩
  induction g using QuotientGroup.induction_on with | H a => ?_
  rw [pslMk_smul, smul_infty_eq_self_iff] at hg
  rw [isParabolic_mk_iff, GeneralLinearGroup.isParabolic_iff_of_upperTriangular hg] at hpar
  obtain ⟨hd, hb⟩ := hpar
  simp only [SpecialLinearGroup.coe_GL_coe_matrix] at hg hd hb
  -- an upper-triangular matrix of determinant one with equal diagonal entries has diagonal `±1`
  have hdet : a 1 1 * a 1 1 = 1 := by
    have := a.det_coe
    rw [det_fin_two, hg, hd] at this
    simpa using this
  rcases mul_self_eq_one_iff.mp hdet with h1 | h1
  · refine ⟨a 0 1, hb, ?_⟩
    rw [upperRightHom_apply]
    refine congrArg _ (SpecialLinearGroup.ext _ _ fun i j ↦ ?_)
    fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, *]
  · refine ⟨-a 0 1, neg_ne_zero.mpr hb, ?_⟩
    have ha : a = -SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) (-a 0 1) :=
      SpecialLinearGroup.ext _ _ fun i j ↦ by
        fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, *]
    rw [upperRightHom_apply, QuotientGroup.eq]
    generalize SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) (-a 0 1) = t at ha ⊢
    subst ha
    simp [inv_neg]

omit [DecidableEq K] in
/-- Conjugating a translation by an upper-triangular matrix `!![a, b; 0, a⁻¹]` rescales it by
`a ^ 2`. -/
private theorem mk_mul_upperRightHom_mul_inv (a : SL(2, K)) (ha : a 1 0 = 0) (x : K) :
    (a : PSL(2, K)) * upperRightHom x * (a : PSL(2, K))⁻¹ = upperRightHom (a 0 0 ^ 2 * x) := by
  have hdet : a 0 0 * a 1 1 = 1 := by
    have := a.det_coe
    rw [det_fin_two, ha] at this
    simpa using this
  rw [mul_inv_eq_iff_eq_mul, upperRightHom_apply, upperRightHom_apply, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two, ha]
  linear_combination -(a 0 0 * x) * hdet

/-- **Conjugating translations by an element fixing `∞`.** An element `g` of `PSL(2, K)` fixing
`∞` acts on `K` by an affine map `k ↦ t ^ 2 * k + s` with `t ≠ 0`; conjugation by `g` therefore
rescales every translation by the same factor `t ^ 2`. -/
theorem exists_conj_upperRightHom_of_smul_infty {g : PSL(2, K)}
    (hg : g • (∞ : OnePoint K) = ∞) :
    ∃ t : K, t ≠ 0 ∧ ∀ x, g * upperRightHom x * g⁻¹ = upperRightHom (t ^ 2 * x) := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  rw [pslMk_smul, smul_infty_eq_self_iff, SpecialLinearGroup.coe_GL_coe_matrix] at hg
  refine ⟨a 0 0, fun h ↦ ?_, mk_mul_upperRightHom_mul_inv a hg⟩
  have := a.det_coe
  rw [det_fin_two, hg, h] at this
  simp at this

/-- An element of `PSL(2, K)` fixing `∞` and commuting with a nonzero translation is itself a
translation. -/
theorem exists_eq_upperRightHom_of_commute {g : PSL(2, K)} (hg : g • (∞ : OnePoint K) = ∞)
    {x : K} (hx : x ≠ 0) (hcomm : Commute g (upperRightHom x)) : ∃ y, g = upperRightHom y := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  rw [pslMk_smul, smul_infty_eq_self_iff, SpecialLinearGroup.coe_GL_coe_matrix] at hg
  have hconj := mk_mul_upperRightHom_mul_inv a hg x
  rw [hcomm.eq, mul_inv_cancel_right] at hconj
  have hsq : a 0 0 ^ 2 = 1 :=
    mul_right_cancel₀ hx (by rw [one_mul]; exact (upperRightHom_injective hconj).symm)
  have hdet : a 0 0 * a 1 1 = 1 := by
    have := a.det_coe
    rw [det_fin_two, hg] at this
    simpa using this
  have h11 : a 1 1 = a 0 0 := by linear_combination a 0 0 * hdet - a 1 1 * hsq
  -- the diagonal entries are both `1` or both `-1`
  rcases sq_eq_one_iff.mp hsq with h | h
  · refine ⟨a 0 1, ?_⟩
    rw [upperRightHom_apply]
    refine congrArg _ (SpecialLinearGroup.ext _ _ fun i j ↦ ?_)
    fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, *]
  · refine ⟨-a 0 1, ?_⟩
    have ha : a = -SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) (-a 0 1) :=
      SpecialLinearGroup.ext _ _ fun i j ↦ by
        fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe, *]
    rw [upperRightHom_apply, QuotientGroup.eq]
    generalize SpecialLinearGroup.transvection (zero_ne_one' (Fin 2)) (-a 0 1) = t at ha ⊢
    subst ha
    simp [inv_neg]

/-- **Normal form of a parabolic element.** If `σ` carries `∞` to the fixed point of a parabolic
`g`, then `σ⁻¹ g σ` is a nonzero translation. -/
theorem IsParabolic.exists_conj_eq_upperRightHom [NeZero (2 : K)] {g : PSL(2, K)}
    (hg : IsParabolic g) {σ : PSL(2, K)} (hσ : σ • (∞ : OnePoint K) = parabolicFixedPoint g) :
    ∃ x ≠ 0, σ⁻¹ * g * σ = upperRightHom x := by
  refine (isParabolic_iff_exists_eq_upperRightHom ?_).mp ?_
  · rw [mul_smul, mul_smul, hσ, hg.smul_parabolicFixedPoint, ← hσ, inv_smul_smul]
  · exact (isParabolic_conj_iff' σ g).mpr hg

omit [DecidableEq K] in
/-- The parabolic elements of `PSL(2, K)` are exactly the conjugates of nonzero translations. -/
theorem isParabolic_iff_exists_conj_upperRightHom [NeZero (2 : K)] {g : PSL(2, K)} :
    IsParabolic g ↔ ∃ σ : PSL(2, K), ∃ x ≠ 0, g = σ * upperRightHom x * σ⁻¹ := by
  classical
  refine ⟨fun hg ↦ ?_, fun ⟨σ, x, hx, hg⟩ ↦
    hg ▸ (isParabolic_conj_iff _ _).mpr (isParabolic_upperRightHom_iff.mpr hx)⟩
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq PSL(2, K) (∞ : OnePoint K) (parabolicFixedPoint g)
  obtain ⟨x, hx, hgx⟩ := hg.exists_conj_eq_upperRightHom hσ
  exact ⟨σ, x, hx, by rw [← hgx]; group⟩

end Matrix.ProjectiveSpecialLinearGroup
