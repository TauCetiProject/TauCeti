/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Algebra.Star.Rosati.Basic
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.Algebra.Central.Quaternion
import TauCeti.Algebra.CentralSimple.SkolemNoether
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Algebra.Star.Rosati.MatrixTrace
import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Positive involutions on simple real matrix algebras

Let `D` be one of the three finite-dimensional real division algebras `ℝ`, `ℂ`, or `ℍ[ℝ]`, and let
`A` be an `ℝ`-star algebra equipped with an `ℝ`-algebra isomorphism
`φ : A ≃ₐ[ℝ] Matrix n n D` (`n` finite) and a cyclic linear functional `t : A →ₗ[ℝ] ℝ` satisfying
`t (x * star x) > 0` for all `x ≠ 0`.  This file shows that `A` admits a *star-preserving*
`ℝ`-algebra isomorphism `e : A ≃ₐ[ℝ] Matrix n n D` identifying `IsRosatiPositive t` with standard
Hermitian positive definiteness (`Matrix.PosDef` for `ℝ` and `ℂ`, and the real part of the
quaternionic Hermitian quadratic form for `ℍ[ℝ]`).

## Main results

* `TauCeti.exists_star_algEquiv_matrix_real`: standardization on `Matrix n n ℝ`.
* `TauCeti.exists_star_algEquiv_matrix_complex`: standardization on `Matrix n n ℂ`.
* `TauCeti.exists_star_algEquiv_matrix_quaternion`: standardization on `Matrix n n ℍ[ℝ]`.

## Implementation notes

The core normalization steps are proved once for an arbitrary finite-dimensional real division
algebra `D` carrying a cyclic positive real-part functional `rePart : D →ₗ[ℝ] ℝ` satisfying
`IsSelfAdjoint a → a = algebraMap ℝ D (rePart a)`:

1. **Skolem–Noether presentation.** Comparing the transported involution `σ` with conjugate
   transposition yields an automorphism `α X = σ (Xᴴ)` of the central simple algebra `M_n(D)` (over
   `ℝ` for `ℝ` and `ℍ[ℝ]`, and over `ℂ` for `ℂ` after showing `σ (I • 1) = -I • 1`).
   `TauCeti.exists_unit_conj_of_algEquiv` writes `σ X = u * Xᴴ * u⁻¹` with `uᴴ = μ • u` and
   `star μ * μ = 1`.
2. **Hermitian normalization.** For `ℂ`, rescaling `u` by `I` (if `μ = -1`) or `1 + μ` makes `u`
   Hermitian.  For `ℝ` and `ℍ[ℝ]`, the skew-Hermitian case `uᴴ = -u` is ruled out via
   `TauCeti.stdMatrixTrace_rankOne_mul_conj` on rank-one matrices `X i j = v i * star (w j)`.
3. **Square-root conjugation.** For Hermitian `u`, rank-one evaluation forces either `u` or `-u` to
   be `IsRosatiPositive` for `stdMatrixTrace`.  Applying `TauCeti.rosatiPositiveSquareRoot` gives
   a Hermitian square root `r` with `r * r = ±u`, and conjugating by `r` sends `σ` to
   `conjTranspose` while preserving the cyclic trace.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), §8.4.
* M. Lipnowski and J. Tsimerman, *Algorithms for abelian varieties*, §4.3.2.
-/

public section

open scoped Matrix ComplexOrder _root_.Quaternion

namespace TauCeti

/-! ### Shared Skolem–Noether and Hermitian normalization steps -/

section SharedNormalization

/-- A nonzero rank-one matrix `X i j = v i * star (w j)` over a division ring. -/
private theorem rankOne_ne_zero {D : Type*} [DivisionRing D] [StarRing D] {n : Type*}
    {v w : n → D} (hv : v ≠ 0) (hw : w ≠ 0) :
    Matrix.of (fun i j ↦ v i * star (w j)) ≠ (0 : Matrix n n D) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv; obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hw
  intro h0
  have h := congrFun (congrFun h0 i₀) j₀
  simp only [Matrix.of_apply, Matrix.zero_apply, mul_eq_zero, star_eq_zero] at h
  exact h.elim hi₀ hj₀

/-- Inner `ℝ`-algebra automorphism `X ↦ r⁻¹ * X * r` induced by a unit `r`. -/
private def innerConjAlgEquiv {R : Type*} [Ring R] [Algebra ℝ R] (r : Rˣ) : R ≃ₐ[ℝ] R where
  toFun X := (↑r⁻¹ : R) * X * (r : R)
  invFun Y := (r : R) * Y * (↑r⁻¹ : R)
  left_inv X := by simp [← mul_assoc]
  right_inv Y := by simp [mul_assoc]
  map_mul' X Y := by simp only [mul_assoc, Units.mul_inv_cancel_left]
  map_add' X Y := by simp only [mul_add, add_mul]
  commutes' k := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, r.inv_mul]

/-- **Skolem–Noether presentation of an involution on a central simple algebra.** Given an
`F`-algebra automorphism `α` of a finite-dimensional central simple `F`-star algebra `M` such that
`X ↦ α (star X)` is an involution, `α X = u * X * u⁻¹` for a unit `u : Mˣ` satisfying
`star u = μ • u` with `star μ * μ = 1`. -/
private theorem exists_unit_conj_star_of_central (F : Type*) {M : Type*} [Field F] [StarRing F]
    [Ring M] [Algebra F M] [StarRing M] [StarModule F M] [Algebra.IsCentral F M]
    [IsSimpleRing M] [FiniteDimensional F M] (α : M ≃ₐ[F] M)
    (hinvol : ∀ X : M, α (star (α (star X))) = X) :
    ∃ (u : Mˣ) (μ : F), (∀ X : M, α X = (u : M) * X * (↑u⁻¹ : M)) ∧
      star (u : M) = μ • (u : M) ∧ star μ * μ = 1 := by
  obtain ⟨u, hu⟩ := exists_unit_conj_of_algEquiv F α
  have hcomm (X : M) : ((u : M) * star (↑u⁻¹ : M)) * X = X * ((u : M) * star (↑u⁻¹ : M)) := by
    have h1 : ((u : M) * star (↑u⁻¹ : M)) * X * (star (u : M) * (↑u⁻¹ : M)) = X := by
      have hX := hinvol X; rw [hu, hu, star_mul, star_mul, star_star] at hX
      simpa only [mul_assoc] using hX
    have hinv : (star (u : M) * (↑u⁻¹ : M)) * ((u : M) * star (↑u⁻¹ : M)) = 1 := by
      rw [mul_assoc (star (u : M)), ← mul_assoc (↑u⁻¹ : M), u.inv_mul, one_mul, ← star_mul,
        u.inv_mul, star_one]
    rw [← mul_one (((u : M) * star (↑u⁻¹ : M)) * X), ← hinv, ← mul_assoc, h1]
  have hmem : (u : M) * star (↑u⁻¹ : M) ∈ Subalgebra.center F M :=
    Subalgebra.mem_center_iff.mpr fun X ↦ (hcomm X).symm
  rw [Algebra.IsCentral.center_eq_bot F M, Algebra.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hcu : c • star (u : M) = (u : M) := by
    simpa [← Algebra.smul_def, mul_assoc, ← star_mul] using congrArg (· * star (u : M)) hc
  have hc0 : c ≠ 0 := fun h0 ↦
    one_ne_zero (by simpa [h0] using congrArg (· * (↑u⁻¹ : M)) hcu.symm : (1 : M) = 0)
  have hsu : star (u : M) = c⁻¹ • (u : M) := (eq_inv_smul_iff₀ hc0).mpr hcu
  refine ⟨u, c⁻¹, hu, hsu, ?_⟩
  have hss : (star c⁻¹ * c⁻¹) • (u : M) = (u : M) := by
    have h2 := congrArg star hsu; rwa [star_star, star_smul, hsu, smul_smul, eq_comm] at h2
  exact (algebraMap F M).injective <| by
    simpa [Algebra.algebraMap_eq_smul_one, smul_mul_assoc] using congrArg (· * (↑u⁻¹ : M)) hss

/-- A Hermitian unit `u` whose conjugation `X ↦ u * Xᴴ * u⁻¹` is positive for `stdMatrixTrace`
satisfies `IsRosatiPositive` up to a sign `±u`. -/
private theorem exists_pos_hermitian_unit {D : Type*} [DivisionRing D] [Algebra ℝ D]
    [StarRing D] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {rePart : D →ₗ[ℝ] ℝ}
    (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (hre_sa : ∀ a : D, IsSelfAdjoint a → a = algebraMap ℝ D (rePart a))
    (u : (Matrix n n D)ˣ) (huH : (u : Matrix n n D)ᴴ = u)
    (hpos : ∀ X : Matrix n n D, X ≠ 0 →
      0 < stdMatrixTrace rePart (X * (u : Matrix n n D) * Xᴴ * (↑u⁻¹ : Matrix n n D))) :
    ∃ a : (Matrix n n D)ˣ,
      IsRosatiPositive (stdMatrixTrace rePart) (a : Matrix n n D) ∧
      ∀ X : Matrix n n D,
        (a : Matrix n n D) * Xᴴ * (↑a⁻¹ : Matrix n n D) =
          (u : Matrix n n D) * Xᴴ * (↑u⁻¹ : Matrix n n D) := by
  have huinvH : (↑u⁻¹ : Matrix n n D)ᴴ = ↑u⁻¹ := IsSelfAdjoint.of_mul_eq_one huH u.mul_inv
  have hre1 : rePart 1 = 1 :=
    ((algebraMap ℝ D).injective (by simpa using hre_sa 1 (IsSelfAdjoint.one D))).symm
  let v₀ : n → D := Pi.single (Classical.arbitrary n) 1
  have hv₀ : v₀ ≠ 0 := fun h ↦ by simpa [v₀] using congrFun h (Classical.arbitrary n)
  set α : ℝ := rePart (∑ i : n, ∑ m : n, star (v₀ i) * (↑u⁻¹ : Matrix n n D) i m * v₀ m)
  have hsum_eq (M : Matrix n n D) (v : n → D) :
      ∑ j : n, ∑ k : n, star (v j) * M j k * v k = star v ⬝ᵥ M *ᵥ v := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]
  have hprod (w : n → D) (hw : w ≠ 0) :
      0 < α * rePart (∑ j : n, ∑ k : n, star (w j) * (u : Matrix n n D) j k * w k) := by
    have h1 := hpos (Matrix.of fun i j ↦ v₀ i * star (w j)) (rankOne_ne_zero hv₀ hw)
    rw [stdMatrixTrace_rankOne_mul_conj hre_cyclic u v₀ w] at h1
    set q1 := ∑ i : n, ∑ m : n, star (v₀ i) * (↑u⁻¹ : Matrix n n D) i m * v₀ m
    set q2 := ∑ j : n, ∑ k : n, star (w j) * (u : Matrix n n D) j k * w k
    have hq1 : q1 = algebraMap ℝ D (rePart q1) := hre_sa q1 (by
      dsimp only [q1]; rw [hsum_eq]
      exact Matrix.IsHermitian.star_dotProduct_mulVec_comm huinvH v₀ v₀)
    have hq2 : q2 = algebraMap ℝ D (rePart q2) := hre_sa q2 (by
      dsimp only [q2]; rw [hsum_eq]
      exact Matrix.IsHermitian.star_dotProduct_mulVec_comm huH w w)
    have hmul : rePart (q1 * q2) = rePart q1 * rePart q2 := by
      (conv_lhs => rw [hq1, hq2])
      rw [← map_mul, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, hre1, mul_one]
    rwa [hmul] at h1
  have hα0 : α ≠ 0 := fun h0 ↦ lt_irrefl 0 (by simpa [h0] using hprod v₀ hv₀)
  rcases lt_or_gt_of_ne hα0 with hlt | hgt
  · refine ⟨-u, (isRosatiPositive_stdMatrixTrace_iff hre_cyclic _).mpr ⟨by
      rw [Matrix.IsHermitian, Units.val_neg, Matrix.conjTranspose_neg, huH], fun w hw ↦ ?_⟩,
      fun _ ↦ by simp⟩
    have hp := hprod w hw
    have hneg : rePart (∑ j : n, ∑ k : n, star (w j) * (-(u : Matrix n n D)) j k * w k) =
        -rePart (∑ j : n, ∑ k : n, star (w j) * (u : Matrix n n D) j k * w k) := by
      simp only [Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib, map_neg]
    rw [Units.val_neg, hneg]; nlinarith
  · exact ⟨u, (isRosatiPositive_stdMatrixTrace_iff hre_cyclic _).mpr
      ⟨huH, fun w hw ↦ pos_of_mul_pos_right (hprod w hw) hgt.le⟩, fun _ ↦ rfl⟩

/-- Given an `ℝ`-algebra isomorphism `φ : A ≃ₐ[ℝ] Matrix n n D` under which `t` is a positive
scalar multiple of `stdMatrixTrace rePart` and `star` is `X ↦ u * Xᴴ * u⁻¹` for a Hermitian
unit `u`, conjugating by the internal positive square root of `±u` yields a star-preserving
`ℝ`-algebra isomorphism matching `IsRosatiPositive t` with
`IsRosatiPositive (stdMatrixTrace rePart)`. -/
private theorem exists_star_algEquiv_matrix_of_hermitian_unit {A D : Type*}
    [Ring A] [Algebra ℝ A] [StarRing A] [DivisionRing D] [Algebra ℝ D] [StarRing D]
    [Module.Finite ℝ D] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {rePart : D →ₗ[ℝ] ℝ}
    (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (hre_pos : ∀ a : D, a ≠ 0 → 0 < rePart (a * star a))
    (hre_sa : ∀ a : D, IsSelfAdjoint a → a = algebraMap ℝ D (rePart a))
    (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
    (ht : ∀ x : A, t x = c * stdMatrixTrace rePart (φ x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x))
    (u : (Matrix n n D)ˣ) (huH : (u : Matrix n n D)ᴴ = u)
    (hσ : ∀ x : A, φ (star x) = (u : Matrix n n D) * (φ x)ᴴ * (↑u⁻¹ : Matrix n n D)) :
    ∃ e : A ≃ₐ[ℝ] Matrix n n D,
      (∀ x : A, e (star x) = star (e x)) ∧
      ∀ s : A, IsRosatiPositive t s ↔ IsRosatiPositive (stdMatrixTrace rePart) (e s) := by
  have hMpos (X : Matrix n n D) (hX : X ≠ 0) :
      0 < stdMatrixTrace rePart (X * (u : Matrix n n D) * Xᴴ * (↑u⁻¹ : Matrix n n D)) := by
    have h1 := hpos (φ.symm X) (fun h ↦ hX (by simpa using congrArg φ h))
    rw [ht, map_mul, hσ, AlgEquiv.apply_symm_apply, ← mul_assoc, ← mul_assoc] at h1
    exact pos_of_mul_pos_right h1 hc.le
  obtain ⟨a, haPos, haConj⟩ := exists_pos_hermitian_unit hre_cyclic hre_sa u huH hMpos
  obtain ⟨_, r, hrPos, hrsq, -, -, -, -⟩ := rosatiPositiveSquareRoot (stdMatrixTrace rePart)
    (stdMatrixTrace_cyclic hre_cyclic) (fun _ hX ↦ stdMatrixTrace_pos hre_pos hX)
    (a : Matrix n n D) haPos
  set R := (r : Matrix n n D); set Rinv := (↑r⁻¹ : Matrix n n D)
  have hrH : Rᴴ = R := hrPos.isSelfAdjoint
  have hrInvH : Rinvᴴ = Rinv := IsSelfAdjoint.of_mul_eq_one hrH r.mul_inv
  have haInv : (↑a⁻¹ : Matrix n n D) = Rinv * Rinv := by
    have hmul : (a : Matrix n n D) * (Rinv * Rinv) = 1 := by
      rw [← hrsq, mul_assoc R R, ← mul_assoc R Rinv, r.mul_inv, one_mul, r.mul_inv]
    simpa [mul_assoc] using (congrArg ((↑a⁻¹ : Matrix n n D) * ·) hmul).symm
  let e : A ≃ₐ[ℝ] Matrix n n D := φ.trans (innerConjAlgEquiv r)
  have heStar (x : A) : e (star x) = star (e x) := by
    change Rinv * φ (star x) * R = (Rinv * φ x * R)ᴴ
    rw [hσ, ← haConj, ← hrsq, haInv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hrH,
      hrInvH]
    simp only [mul_assoc, R, Rinv, Units.inv_mul_cancel_left, r.inv_mul, mul_one]
  have heTrace : t = (c • stdMatrixTrace rePart).comp e.toLinearMap := by
    ext x
    have htr : stdMatrixTrace rePart (Rinv * φ x * R) = stdMatrixTrace rePart (φ x) := by
      rw [stdMatrixTrace_cyclic hre_cyclic (Rinv * φ x) R, ← mul_assoc, r.mul_inv, one_mul]
    rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearMap.smul_apply, smul_eq_mul]
    exact (ht x).trans (congrArg (c * ·) htr.symm)
  refine ⟨e, heStar, fun s ↦ ?_⟩
  rw [heTrace, isRosatiPositive_iff_of_algEquiv e heStar, isRosatiPositive_iff,
    isRosatiPositive_iff]
  exact and_congr_right fun _ ↦ forall₂_congr fun X _ ↦
    ⟨fun h ↦ pos_of_mul_pos_right h hc.le, fun h ↦ mul_pos hc h⟩

/-- Shared trace-proportionality step for `ℝ`-central division algebras (`ℝ` and `ℍ[ℝ]`): if every
cyclic functional `τ` on `D` satisfies `τ a = τ 1 * rePart a` with `rePart 1 = 1`, then a cyclic
positive functional `t` on `A ≃ₐ[ℝ] Matrix n n D` is a positive multiple of
`stdMatrixTrace rePart ∘ φ`. -/
private theorem exists_pos_const_stdMatrixTrace_of_cyclic {A D : Type*} [Ring A] [Algebra ℝ A]
    [StarRing A] [Ring D] [Nontrivial D] [Algebra ℝ D] {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (rePart : D →ₗ[ℝ] ℝ) (hre1 : rePart 1 = 1)
    (hD_cyc : ∀ τ : D →ₗ[ℝ] ℝ, (∀ a b : D, τ (a * b) = τ (b * a)) → ∀ a : D, τ a = τ 1 * rePart a)
    (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ)
    (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : A, t x = c * stdMatrixTrace rePart (φ x) := by
  let tM : Matrix n n D →ₗ[ℝ] ℝ := t.comp φ.symm.toLinearMap
  obtain ⟨τ, hτ_cyc, hτ⟩ := cyclic_linearMap_matrix_eq_trace tM fun X Y ↦ by
    simp only [tM, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, hcyclic]
  have hc : 0 < τ 1 := by
    have h1 : 0 < t 1 := by
      simpa using hpos 1 fun h0 ↦ one_ne_zero (α := Matrix n n D) (by simpa using congrArg φ h0)
    have ht1 := hτ 1
    simp only [tM, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one,
      Matrix.trace_one] at ht1
    rw [ht1, hD_cyc τ hτ_cyc, show (Fintype.card n : D) = (Fintype.card n : ℝ) • (1 : D) by
      rw [Algebra.smul_def, mul_one, map_natCast], map_smul, smul_eq_mul, hre1, mul_one,
      mul_comm] at h1
    exact pos_of_mul_pos_right h1 (Nat.cast_pos.mpr Fintype.card_pos).le
  refine ⟨τ 1, hc, fun x ↦ ?_⟩
  have h1 := hτ (φ x)
  simp only [tM, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply] at h1
  rw [h1, hD_cyc τ hτ_cyc, stdMatrixTrace_apply]

/-- Shared `ℝ`-central Skolem–Noether step: on `Matrix n n D` central simple over `ℝ`, any
`ℝ`-linear involution `star` is `X ↦ u * Xᴴ * u⁻¹` with `uᴴ = u` or `uᴴ = -u`. -/
private theorem exists_unit_conj_real_central {A D : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    [StarModule ℝ A] [DivisionRing D] [Algebra ℝ D] [StarRing D] [StarModule ℝ D]
    [Algebra.IsCentral ℝ D] [FiniteDimensional ℝ D] {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (φ : A ≃ₐ[ℝ] Matrix n n D) :
    ∃ u : (Matrix n n D)ˣ,
      ((u : Matrix n n D)ᴴ = u ∨ (u : Matrix n n D)ᴴ = -u) ∧
      ∀ x : A, φ (star x) = (u : Matrix n n D) * (φ x)ᴴ * (↑u⁻¹ : Matrix n n D) := by
  let α : Matrix n n D ≃ₐ[ℝ] Matrix n n D :=
    { toFun := fun X ↦ φ (star (φ.symm Xᴴ)), invFun := fun Y ↦ (φ (star (φ.symm Y)))ᴴ
      left_inv := fun X ↦ by simp, right_inv := fun Y ↦ by simp
      map_mul' := fun X Y ↦ by simp [star_mul], map_add' := fun X Y ↦ by simp
      commutes' := fun r ↦ by simp [Algebra.algebraMap_eq_smul_one, star_smul] }
  obtain ⟨u, μ, hu, huμ, hμsq⟩ := exists_unit_conj_star_of_central ℝ α fun X ↦ by
    simp [α, Matrix.star_eq_conjTranspose]
  refine ⟨u, ?_, fun x ↦ by simpa [α] using hu (φ x)ᴴ⟩
  rw [← Matrix.star_eq_conjTranspose]
  rcases mul_self_eq_one_iff.mp (by simpa using hμsq) with rfl | rfl
  · exact Or.inl (by simpa using huμ)
  · exact Or.inr (by simpa using huμ)

end SharedNormalization

/-! ### Standardization for real, complex, and quaternionic matrix factors -/

section RealFactor

/-- A skew-symmetric real unit `uᵀ = -u` cannot define a positive involution. -/
private theorem not_pos_of_skewSymmetric_real {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (u : (Matrix n n ℝ)ˣ) (hskew : (u : Matrix n n ℝ)ᴴ = -u)
    (hpos : ∀ X : Matrix n n ℝ, X ≠ 0 →
      0 < stdMatrixTrace (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
        (X * (u : Matrix n n ℝ) * Xᴴ * (↑u⁻¹ : Matrix n n ℝ))) :
    False := by
  let v₀ : n → ℝ := Pi.single (Classical.arbitrary n) 1
  have hv₀ : v₀ ≠ 0 := fun h ↦ by simpa [v₀] using congrFun h (Classical.arbitrary n)
  have hposX := hpos (Matrix.of fun i j ↦ v₀ i * star (v₀ j)) (rankOne_ne_zero hv₀ hv₀)
  rw [stdMatrixTrace_rankOne_mul_conj (fun a b ↦ mul_comm a b) u v₀ v₀] at hposX
  have hQ0 : ∑ j : n, ∑ k : n, star (v₀ j) * (u : Matrix n n ℝ) j k * v₀ k = 0 := by
    have hswap : ∑ j : n, ∑ k : n, star (v₀ j) * (u : Matrix n n ℝ) j k * v₀ k =
        -(∑ j : n, ∑ k : n, star (v₀ j) * (u : Matrix n n ℝ) j k * v₀ k) := by
      conv_lhs => rw [Finset.sum_comm]
      simp_rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      have hjk : (u : Matrix n n ℝ) k j = -(u : Matrix n n ℝ) j k := by
        simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hskew j) k
      rw [hjk]; simp only [star_trivial]; ring
    linarith
  rw [hQ0, mul_zero, map_zero] at hposX; exact lt_irrefl 0 hposX

/-- Trivial standardization when the matrix index type `n` is empty. -/
private theorem exists_star_algEquiv_empty {A D : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    [Ring D] [Algebra ℝ D] [StarRing D] {n : Type*} [Fintype n] [DecidableEq n] [IsEmpty n]
    (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ) (P : Matrix n n D → Prop)
    (hP : ∀ X : Matrix n n D, P X) :
    ∃ e : A ≃ₐ[ℝ] Matrix n n D,
      (∀ x : A, e (star x) = star (e x)) ∧ ∀ s : A, IsRosatiPositive t s ↔ P (e s) :=
  have : Subsingleton A := φ.injective.subsingleton
  ⟨φ, fun _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨fun _ ↦ hP _, fun _ ↦
    isRosatiPositive_iff.mpr ⟨Subsingleton.elim _ _, fun x hx ↦ absurd (Subsingleton.elim x 0) hx⟩⟩⟩

/-- Standardization of a positive involution and cyclic positive trace on a real matrix algebra
`Matrix n n ℝ`. -/
theorem exists_star_algEquiv_matrix_real {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℝ)
    (t : A →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ e : A ≃ₐ[ℝ] Matrix n n ℝ,
      (∀ x : A, e (star x) = star (e x)) ∧
      ∀ s : A, IsRosatiPositive t s ↔ (e s).PosDef := by
  rcases isEmpty_or_nonempty n with hempty | hne
  · exact exists_star_algEquiv_empty φ t _ fun _ ↦
      Matrix.posDef_iff_dotProduct_mulVec.mpr
        ⟨Subsingleton.elim _ _, fun v hv ↦ absurd (Subsingleton.elim v 0) hv⟩
  · have : StarModule ℝ A := starModule_of_trace_mul_star_pos t hpos
    obtain ⟨c, hc, ht⟩ := exists_pos_const_stdMatrixTrace_of_cyclic (LinearMap.id : ℝ →ₗ[ℝ] ℝ) rfl
      (fun τ _ a ↦ by simpa [mul_comm] using τ.map_smul a (1 : ℝ)) φ t hcyclic hpos
    obtain ⟨u, huSign, hσ⟩ := exists_unit_conj_real_central φ
    have huH : (u : Matrix n n ℝ)ᴴ = u := huSign.resolve_right fun hskew ↦
      not_pos_of_skewSymmetric_real u hskew fun X hX ↦ by
        have h1 := hpos (φ.symm X) (fun h ↦ hX (by simpa using congrArg φ h))
        rw [ht, map_mul, hσ, AlgEquiv.apply_symm_apply, ← mul_assoc, ← mul_assoc] at h1
        exact pos_of_mul_pos_right h1 hc.le
    obtain ⟨e, heStar, hePos⟩ := exists_star_algEquiv_matrix_of_hermitian_unit
      (fun a b ↦ mul_comm a b) (fun a ha ↦ by simpa using mul_self_pos.mpr ha) (fun _ _ ↦ rfl)
      φ t c hc ht hpos u huH hσ
    exact ⟨e, heStar, fun s ↦ (hePos s).trans (isRosatiPositive_stdMatrixTrace_real_iff (e s))⟩

end RealFactor

section ComplexFactor

/-- On `Matrix n n ℂ` (`n` nonempty), any positive real-linear involution conjugates `I • 1`. -/
private theorem star_I_smul_one_eq_neg {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (t : A →ₗ[ℝ] ℝ) (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    φ (star (φ.symm (Complex.I • (1 : Matrix n n ℂ)))) = -(Complex.I • (1 : Matrix n n ℂ)) := by
  let M := Matrix n n ℂ
  let z : M := Complex.I • (1 : M)
  let w : M := φ (star (φ.symm z))
  have hw_center : w ∈ Subalgebra.center ℂ M := Subalgebra.mem_center_iff.mpr fun Y ↦ by
    have hcomm : z * φ (star (φ.symm Y)) = φ (star (φ.symm Y)) * z := by simp [z]
    simpa only [map_mul, star_mul, AlgEquiv.symm_apply_apply, star_star,
      AlgEquiv.apply_symm_apply] using congrArg (fun X ↦ φ (star (φ.symm X))) hcomm
  rw [Algebra.IsCentral.center_eq_bot ℂ M, Algebra.mem_bot] at hw_center
  obtain ⟨c, hc⟩ := hw_center
  have hc_sq : c * c = -1 := (algebraMap ℂ M).injective <| by
    rw [map_mul, hc, map_neg, map_one]
    calc w * w = φ (star (φ.symm (z * z))) := by simp [w, map_mul, star_mul]
      _ = -1 := by simp [z, smul_smul, Complex.I_mul_I]
  have h0 : (c - Complex.I) * (c + Complex.I) = 0 := by
    calc (c - Complex.I) * (c + Complex.I) = c * c - Complex.I * Complex.I := by ring
      _ = 0 := by rw [hc_sq, Complex.I_mul_I, sub_self]
  rcases (mul_eq_zero.mp h0).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left with rfl | rfl
  · exfalso
    have hz_ne : φ.symm z ≠ 0 := fun h0 ↦ Complex.I_ne_zero <| by
      simpa [z, M] using congrFun (congrFun (congrArg φ h0)
        (Classical.arbitrary n)) (Classical.arbitrary n)
    have h1 := hpos (φ.symm z) hz_ne
    have h2 : φ.symm z * star (φ.symm z) = -1 := φ.injective <| by
      rw [map_mul, AlgEquiv.apply_symm_apply, show φ (star (φ.symm z)) = Complex.I • (1 : M) by
        simpa [w, Algebra.algebraMap_eq_smul_one] using hc.symm]
      simp [z, smul_smul, Complex.I_mul_I]
    have hone : 0 < t 1 := by
      simpa using hpos 1 fun h0 ↦ one_ne_zero (α := M) (by simpa using congrArg φ h0)
    rw [h2, map_neg] at h1; linarith
  · simpa [w, z, Algebra.algebraMap_eq_smul_one, neg_smul] using hc.symm

/-- Any positive real-linear involution on `Matrix n n ℂ` acts as complex conjugation on scalar
matrices `c • 1`. -/
private theorem star_scalar_complex {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    [StarModule ℝ A] {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (hI : φ (star (φ.symm (Complex.I • (1 : Matrix n n ℂ)))) = -(Complex.I • (1 : Matrix n n ℂ)))
    (c : ℂ) :
    φ (star (φ.symm (c • (1 : Matrix n n ℂ)))) = (star c) • (1 : Matrix n n ℂ) := by
  have hsm : c • (1 : Matrix n n ℂ) =
      c.re • (1 : Matrix n n ℂ) + c.im • (Complex.I • (1 : Matrix n n ℂ)) := by
    ext i j; by_cases hij : i = j <;> simp [hij, Complex.real_smul]
  rw [hsm, map_add, map_smul, map_smul, star_add, star_smul, star_smul, star_trivial c.re,
    star_trivial c.im, map_add, map_smul, map_smul, map_one, star_one, map_one, hI, smul_neg]
  ext i j; by_cases hij : i = j <;> simp [hij, Complex.real_smul, Complex.ext_iff]

/-- Rescaling a unit `u` with `uᴴ = μ • u` and `star μ * μ = 1` over `ℂ` to a Hermitian unit
defining the same conjugation. -/
private theorem exists_hermitian_rescale_complex {n : Type*} [Fintype n] [DecidableEq n]
    (u : (Matrix n n ℂ)ˣ) (μ : ℂ) (huμ : (u : Matrix n n ℂ)ᴴ = μ • (u : Matrix n n ℂ))
    (hμsq : star μ * μ = 1) :
    ∃ u' : (Matrix n n ℂ)ˣ,
      (u' : Matrix n n ℂ)ᴴ = u' ∧
      ∀ X : Matrix n n ℂ,
        (u' : Matrix n n ℂ) * X * (↑u'⁻¹ : Matrix n n ℂ) =
          (u : Matrix n n ℂ) * X * (↑u⁻¹ : Matrix n n ℂ) := by
  let ζ : ℂ := if μ = -1 then Complex.I else 1 + μ
  have hζ0 : ζ ≠ 0 := by
    by_cases h : μ = -1
    · simp [ζ, h, Complex.I_ne_zero]
    · simp only [ζ, h, ↓reduceIte]; exact fun h0 ↦ h (eq_neg_of_add_eq_zero_right h0)
  refine ⟨⟨ζ • (u : Matrix n n ℂ), ζ⁻¹ • (↑u⁻¹ : Matrix n n ℂ),
      by simp [smul_smul, inv_mul_cancel₀ hζ0], by simp [smul_smul, mul_inv_cancel₀ hζ0]⟩,
    ?_, fun X ↦ by
      change (ζ • (u : Matrix n n ℂ)) * X * (ζ⁻¹ • (↑u⁻¹ : Matrix n n ℂ)) = _
      simp [smul_smul, inv_mul_cancel₀ hζ0]⟩
  change (ζ • (u : Matrix n n ℂ))ᴴ = ζ • (u : Matrix n n ℂ)
  rw [Matrix.conjTranspose_smul, huμ, smul_smul]; congr 1
  by_cases h : μ = -1
  · simp [ζ, h]
  · simp only [ζ, h, ↓reduceIte, star_add, star_one, add_mul, one_mul]
    rw [add_comm 1 μ]; simpa using congrArg (μ + ·) hμsq

/-- A cyclic, star-invariant positive functional on `Matrix n n ℂ` (`n` nonempty) is a positive
real multiple of `stdMatrixTrace Complex.reLm`. -/
private theorem trace_eq_mul_stdMatrixTrace_complex {A : Type*} [Ring A] [Algebra ℝ A]
    [StarRing A] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (hI : φ (star (φ.symm (Complex.I • (1 : Matrix n n ℂ)))) = -(Complex.I • (1 : Matrix n n ℂ)))
    (t' : A →ₗ[ℝ] ℝ) (hcyc' : ∀ x y : A, t' (x * y) = t' (y * x))
    (hstar' : ∀ x : A, t' (star x) = t' x)
    (hpos' : ∀ x : A, x ≠ 0 → 0 < t' (x * star x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : A, t' x = c * stdMatrixTrace Complex.reLm (φ x) := by
  let tM : Matrix n n ℂ →ₗ[ℝ] ℝ := t'.comp φ.symm.toLinearMap
  obtain ⟨τ, -, hτ⟩ := cyclic_linearMap_matrix_eq_trace tM fun X Y ↦ by
    simp only [tM, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, hcyc']
  have hc : 0 < τ 1 := by
    have h1 : 0 < t' 1 := by
      simpa using hpos' 1 fun h0 ↦ one_ne_zero (α := Matrix n n ℂ) (by simpa using congrArg φ h0)
    have ht1 := hτ 1
    simp only [tM, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one,
      Matrix.trace_one] at ht1
    rw [ht1, show (Fintype.card n : ℂ) = (Fintype.card n : ℝ) • (1 : ℂ) by
      simp [Complex.real_smul], map_smul, smul_eq_mul] at h1
    exact pos_of_mul_pos_right h1 (Nat.cast_nonneg _)
  have hτI : τ Complex.I = 0 := by
    have h1 : tM (Complex.I • (1 : Matrix n n ℂ)) = (Fintype.card n : ℝ) * τ Complex.I := by
      rw [hτ, Matrix.trace_smul, Matrix.trace_one,
        show (Complex.I • (Fintype.card n : ℂ)) = (Fintype.card n : ℝ) • Complex.I by
          simp [Complex.real_smul, mul_comm], map_smul, smul_eq_mul]
    have h2 : tM (Complex.I • (1 : Matrix n n ℂ)) = -tM (Complex.I • (1 : Matrix n n ℂ)) := by
      simp only [tM, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
      conv_lhs => rw [← hstar', ← AlgEquiv.symm_apply_apply φ (star _), hI, map_neg, map_neg]
    exact (mul_eq_zero.mp (by linarith : (Fintype.card n : ℝ) * τ Complex.I = 0)).resolve_left
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine ⟨τ 1, hc, fun x ↦ ?_⟩
  have h1 := hτ (φ x)
  simp only [tM, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply] at h1
  rw [h1, stdMatrixTrace_apply]
  conv_lhs => rw [show Matrix.trace (φ x) =
    (Matrix.trace (φ x)).re • (1 : ℂ) + (Matrix.trace (φ x)).im • Complex.I by
    simp [Complex.real_smul, Complex.re_add_im]]
  rw [map_add, map_smul, map_smul, hτI, smul_zero, add_zero, smul_eq_mul, mul_comm]; rfl

/-- Standardization of a positive involution and cyclic positive trace on a complex matrix algebra
`Matrix n n ℂ`. -/
theorem exists_star_algEquiv_matrix_complex {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (t : A →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ e : A ≃ₐ[ℝ] Matrix n n ℂ,
      (∀ x : A, e (star x) = star (e x)) ∧
      ∀ s : A, IsRosatiPositive t s ↔ (e s).PosDef := by
  rcases isEmpty_or_nonempty n with hempty | hne
  · exact exists_star_algEquiv_empty φ t _ fun _ ↦
      Matrix.posDef_iff_dotProduct_mulVec.mpr
        ⟨Subsingleton.elim _ _, fun v hv ↦ absurd (Subsingleton.elim v 0) hv⟩
  · have : StarModule ℝ A := starModule_of_trace_mul_star_pos t hpos
    let t' : A →ₗ[ℝ] ℝ :=
      { toFun := fun x ↦ (t x + t (star x)) / 2
        map_add' := fun x y ↦ by simp only [star_add, map_add]; ring
        map_smul' := fun c x ↦ by
          simp only [star_smul, star_trivial, map_smul, smul_eq_mul, RingHom.id_apply]; ring }
    have ht' (x : A) : t' x = (t x + t (star x)) / 2 := rfl
    have hcyc' (x y : A) : t' (x * y) = t' (y * x) := by
      simp only [ht', star_mul, hcyclic x y, hcyclic (star y) (star x)]
    have hstar' (x : A) : t' (star x) = t' x := by simp only [ht', star_star, add_comm]
    have hpos' (x : A) (hx : x ≠ 0) : 0 < t' (x * star x) := by
      have h := hpos x hx; simp only [ht', star_mul, star_star]; linarith
    have hI := star_I_smul_one_eq_neg φ t' hpos'
    obtain ⟨c, hc, ht⟩ := trace_eq_mul_stdMatrixTrace_complex φ hI t' hcyc' hstar' hpos'
    let α : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ :=
      { toFun := fun X ↦ φ (star (φ.symm Xᴴ)), invFun := fun Y ↦ (φ (star (φ.symm Y)))ᴴ
        left_inv := fun X ↦ by simp, right_inv := fun Y ↦ by simp
        map_mul' := fun X Y ↦ by simp [star_mul], map_add' := fun X Y ↦ by simp
        commutes' := fun z ↦ by
          simp only [Algebra.algebraMap_eq_smul_one, Matrix.conjTranspose_smul,
            Matrix.conjTranspose_one, star_scalar_complex φ hI, star_star] }
    obtain ⟨u, μ, hu, huμ, hμsq⟩ := exists_unit_conj_star_of_central ℂ α fun X ↦ by
      simp [α, Matrix.star_eq_conjTranspose]
    obtain ⟨u', hu'H, hu'conj⟩ := exists_hermitian_rescale_complex u μ
      (by rw [← Matrix.star_eq_conjTranspose]; exact huμ) hμsq
    have hσ (x : A) : φ (star x) = (u' : Matrix n n ℂ) * (φ x)ᴴ * (↑u'⁻¹ : Matrix n n ℂ) := by
      rw [hu'conj]; simpa [α] using hu (φ x)ᴴ
    obtain ⟨e, heStar, hePos⟩ := exists_star_algEquiv_matrix_of_hermitian_unit
      (rePart := Complex.reLm) (fun a b ↦ by rw [mul_comm])
      (fun a ha ↦ by simpa [Complex.normSq_apply] using Complex.normSq_pos.mpr ha)
      (fun a ha ↦ Complex.ext rfl (by
        have := congrArg Complex.im ha; simp only [RCLike.star_def, Complex.conj_im] at this
        simp [show a.im = 0 by linarith]))
      φ t' c hc ht hpos' u' hu'H hσ
    exact ⟨e, heStar, fun s ↦ by
      rw [← isRosatiPositive_iff_of_symmetrize ht' hcyclic, hePos,
        isRosatiPositive_stdMatrixTrace_complex_iff]⟩

end ComplexFactor

section QuaternionFactor

/-- Every pure imaginary quaternion `r` admits a nonzero pure imaginary quaternion `q` satisfying
`star q * r * q = -(q.normSq • r)`. -/
private theorem exists_pure_quaternion_neg_conj (r : ℍ[ℝ]) (hr : r.re = 0) :
    ∃ q : ℍ[ℝ], q ≠ 0 ∧ star q * r * q = -(Quaternion.normSq q • r) := by
  by_cases h : r.imI = 0 ∧ r.imJ = 0
  · refine ⟨⟨0, 1, 0, 0⟩, by intro h0; simpa using congrArg QuaternionAlgebra.imI h0, ?_⟩
    ext <;> simp [Quaternion.normSq_def', hr, h.1, h.2]
  · refine ⟨⟨0, -r.imJ, r.imI, 0⟩, fun h0 ↦ h ⟨congrArg QuaternionAlgebra.imJ h0,
      neg_eq_zero.mp (congrArg QuaternionAlgebra.imI h0)⟩, ?_⟩
    ext <;> simp [Quaternion.normSq_def', hr] <;> ring

/-- Every cyclic `ℝ`-linear functional on `ℍ[ℝ]` is a scalar multiple of `QuaternionAlgebra.re`. -/
private theorem cyclic_quaternion_eq_mul_re (τ : ℍ[ℝ] →ₗ[ℝ] ℝ)
    (hcyc : ∀ a b : ℍ[ℝ], τ (a * b) = τ (b * a)) (q : ℍ[ℝ]) :
    τ q = τ 1 * q.re := by
  let qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩; let qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩; let qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩
  have hzero (x y z : ℍ[ℝ]) (h : (2 : ℝ) • x = y * z - z * y) : τ x = 0 := by
    have h0 : 2 * τ x = 0 := by
      simpa [map_smul, smul_eq_mul, map_sub, hcyc y z] using congrArg τ h
    linarith
  have hdecomp : q = q.re • (1 : ℍ[ℝ]) + q.imI • qi + q.imJ • qj + q.imK • qk := by
    ext <;> simp [qi, qj, qk]
  conv_lhs => rw [hdecomp]
  simp [hzero qi qj qk (by ext <;> norm_num [qi, qj, qk]),
    hzero qj qk qi (by ext <;> norm_num [qi, qj, qk]),
    hzero qk qi qj (by ext <;> norm_num [qi, qj, qk]), mul_comm]

/-- The quadratic form of a skew-Hermitian quaternionic matrix is purely imaginary. -/
private theorem re_quadForm_eq_zero_of_skewHermitian {n : Type*} [Fintype n]
    {M : Matrix n n ℍ[ℝ]} (hM : Mᴴ = -M) (v : n → ℍ[ℝ]) :
    (∑ i : n, ∑ m : n, star (v i) * M i m * v m).re = 0 := by
  have hskew : star (∑ i : n, ∑ m : n, star (v i) * M i m * v m) =
      -(∑ i : n, ∑ m : n, star (v i) * M i m * v m) := by
    rw [star_sum]; simp_rw [star_sum]
    have hinner (i : n) :
        ∑ m : n, star (star (v i) * M i m * v m) = -(∑ m : n, star (v m) * M m i * v i) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      have him : star (M i m) = -M m i := by
        simpa [Matrix.conjTranspose_apply] using congrFun (congrFun hM m) i
      rw [star_mul, star_mul, star_star, him, neg_mul, mul_neg, mul_assoc]
    simp_rw [hinner, Finset.sum_neg_distrib]; rw [Finset.sum_comm]
  have := congrArg QuaternionAlgebra.re hskew
  simp only [Quaternion.re_star, QuaternionAlgebra.re_neg] at this; linarith

/-- A skew-Hermitian unit `uᴴ = -u` over `ℍ[ℝ]` cannot define a positive involution. -/
private theorem not_pos_of_skewHermitian_quaternion {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (u : (Matrix n n ℍ[ℝ])ˣ) (hskew : (u : Matrix n n ℍ[ℝ])ᴴ = -u)
    (hpos : ∀ X : Matrix n n ℍ[ℝ], X ≠ 0 →
      0 < stdMatrixTrace (QuaternionAlgebra.reₗ (-1) 0 (-1))
        (X * (u : Matrix n n ℍ[ℝ]) * Xᴴ * (↑u⁻¹ : Matrix n n ℍ[ℝ]))) :
    False := by
  have hre_cyc (a b : ℍ[ℝ]) : (QuaternionAlgebra.reₗ (-1) 0 (-1)) (a * b) =
      (QuaternionAlgebra.reₗ (-1) 0 (-1)) (b * a) := by
    simp only [QuaternionAlgebra.reₗ_apply, Quaternion.re_mul]; ring
  set Uinv : Matrix n n ℍ[ℝ] := (↑u⁻¹ : Matrix n n ℍ[ℝ])
  have huinv_skew : Uinvᴴ = -Uinv := by
    have h1 := congrArg (· * Uinv) (congrArg Matrix.conjTranspose u.mul_inv)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_one, hskew, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc, show (u : Matrix n n ℍ[ℝ]) * Uinv = 1 from u.mul_inv,
      Matrix.mul_one, Matrix.one_mul] at h1
    exact neg_eq_iff_eq_neg.mp h1
  let i₀ : n := Classical.arbitrary n; let v₀ : n → ℍ[ℝ] := Pi.single i₀ 1
  have hv₀ : v₀ ≠ 0 := fun h ↦ by simpa [v₀] using congrFun h i₀
  set r : ℍ[ℝ] := ∑ i : n, ∑ m : n, star (v₀ i) * Uinv i m * v₀ m
  set s : ℍ[ℝ] := ∑ j : n, ∑ k : n, star (v₀ j) * (u : Matrix n n ℍ[ℝ]) j k * v₀ k
  have hpos0 : 0 < (r * s).re := by
    have h := hpos (Matrix.of fun i j ↦ v₀ i * star (v₀ j)) (rankOne_ne_zero hv₀ hv₀)
    rwa [stdMatrixTrace_rankOne_mul_conj hre_cyc u v₀ v₀] at h
  obtain ⟨q, hq0, hqconj⟩ := exists_pure_quaternion_neg_conj r
    (re_quadForm_eq_zero_of_skewHermitian huinv_skew v₀)
  let v₁ : n → ℍ[ℝ] := fun i ↦ v₀ i * q
  have hv₁ : v₁ ≠ 0 := fun h ↦ by have := congrFun h i₀; simp [v₁, v₀, hq0] at this
  have hpos1 : 0 < (-(Quaternion.normSq q • r) * s).re := by
    have h := hpos (Matrix.of fun i j ↦ v₁ i * star (v₀ j)) (rankOne_ne_zero hv₁ hv₀)
    rw [stdMatrixTrace_rankOne_mul_conj hre_cyc u v₁ v₀] at h
    have hQ1 : ∑ i : n, ∑ m : n, star (v₁ i) * Uinv i m * v₁ m = star q * r * q := by
      simp only [v₁, r, star_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rwa [hQ1, hqconj] at h
  have hnq : 0 < Quaternion.normSq q :=
    lt_of_not_ge fun h ↦ hq0 (Quaternion.normSq_le_zero.mp h)
  simp only [neg_mul, QuaternionAlgebra.re_neg, smul_mul_assoc, QuaternionAlgebra.re_smul,
    smul_eq_mul] at hpos1
  nlinarith

/-- For a nonzero real quaternion `a`, `(a * star a).re > 0`. -/
private theorem quaternion_re_mul_star_pos {a : ℍ[ℝ]} (ha : a ≠ 0) : 0 < (a * star a).re := by
  rw [Quaternion.self_mul_star, Quaternion.re_coe]
  exact lt_of_not_ge fun h ↦ ha (Quaternion.normSq_le_zero.mp h)

/-- Standardization of a positive involution and cyclic positive trace on a quaternionic matrix
algebra `Matrix n n ℍ[ℝ]`. -/
theorem exists_star_algEquiv_matrix_quaternion {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℍ[ℝ])
    (t : A →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ e : A ≃ₐ[ℝ] Matrix n n ℍ[ℝ],
      (∀ x : A, e (star x) = star (e x)) ∧
      ∀ s : A, IsRosatiPositive t s ↔
        (e s).IsHermitian ∧ ∀ v : n → ℍ[ℝ], v ≠ 0 →
          0 < (∑ j : n, ∑ k : n, star (v j) * (e s) j k * v k).re := by
  rcases isEmpty_or_nonempty n with hempty | hne
  · exact exists_star_algEquiv_empty φ t
      (fun X ↦ X.IsHermitian ∧ ∀ v : n → ℍ[ℝ], v ≠ 0 →
        0 < (∑ j : n, ∑ k : n, star (v j) * X j k * v k).re)
      fun _ ↦ ⟨Subsingleton.elim _ _, fun v hv ↦ absurd (Subsingleton.elim v 0) hv⟩
  · have : StarModule ℝ A := starModule_of_trace_mul_star_pos t hpos
    let reH : ℍ[ℝ] →ₗ[ℝ] ℝ := QuaternionAlgebra.reₗ (-1) 0 (-1)
    have hre_cyc (a b : ℍ[ℝ]) : reH (a * b) = reH (b * a) := by
      simp only [reH, QuaternionAlgebra.reₗ_apply, Quaternion.re_mul]; ring
    obtain ⟨c, hc, ht⟩ := exists_pos_const_stdMatrixTrace_of_cyclic reH rfl
      cyclic_quaternion_eq_mul_re φ t hcyclic hpos
    obtain ⟨u, huSign, hσ⟩ := exists_unit_conj_real_central φ
    have huH : (u : Matrix n n ℍ[ℝ])ᴴ = u := huSign.resolve_right fun hskew ↦
      not_pos_of_skewHermitian_quaternion u hskew fun X hX ↦ by
        have h1 := hpos (φ.symm X) (fun h ↦ hX (by simpa using congrArg φ h))
        rw [ht, map_mul, hσ, AlgEquiv.apply_symm_apply, ← mul_assoc, ← mul_assoc] at h1
        exact pos_of_mul_pos_right h1 hc.le
    obtain ⟨e, heStar, hePos⟩ := exists_star_algEquiv_matrix_of_hermitian_unit hre_cyc
      (fun _ ha ↦ quaternion_re_mul_star_pos ha) (fun _ ha ↦ Quaternion.star_eq_self.mp ha)
      φ t c hc ht hpos u huH hσ
    exact ⟨e, heStar, fun s ↦ (hePos s).trans (isRosatiPositive_stdMatrixTrace_iff hre_cyc (e s))⟩

end QuaternionFactor

end TauCeti
