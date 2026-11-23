/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Algebra.Star.Rosati.Basic
public import TauCeti.LinearAlgebra.Matrix.PosDef.Quaternion
import Mathlib.Algebra.Central.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.SimpleRing.Matrix
import TauCeti.Algebra.Central.Quaternion
import TauCeti.Algebra.CentralSimple.SkolemNoetherStar
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.Algebra.Star.Rosati.MatrixTrace
import TauCeti.Algebra.Star.Rosati.SquareRoot
import TauCeti.Algebra.Star.SelfAdjoint
import TauCeti.Algebra.Star.SelfAdjoint.LinearMap
import TauCeti.LinearAlgebra.Matrix.Trace.Comp

/-!
# Positive involutions on simple real matrix algebras

Let `D` be one of `ℝ`, `ℂ`, or `ℍ[ℝ]`, and let `A` be an `ℝ`-star algebra equipped with an
`ℝ`-algebra isomorphism `φ : A ≃ₐ[ℝ] Matrix n n D` (`n` finite) and a cyclic linear functional
`t : A →ₗ[ℝ] ℝ` satisfying `t (x * star x) > 0` for all `x ≠ 0`. This file constructs a
star-preserving `ℝ`-algebra isomorphism `e : A ≃⋆ₐ[ℝ] Matrix n n D` identifying
`TauCeti.IsRosatiPositive t` with `Matrix.PosDef` (for `ℝ`, `ℂ`) or `Matrix.QuatPosDef`
(for `ℍ[ℝ]`).

## Main results

* `TauCeti.exists_star_algEquiv_matrix_real`, `TauCeti.exists_star_algEquiv_matrix_complex`,
  `TauCeti.exists_star_algEquiv_matrix_quaternion`: star-preserving matrix standardizations and
  positivity comparisons over `ℝ`, `ℂ`, and `ℍ[ℝ]`.

## Implementation notes

Uses `TauCeti.exists_unit_conj_star_of_central` to present `X ↦ φ (star (φ.symm Xᴴ))` as
`u * X * u⁻¹` with `star u = μ • u`, makes `u` Hermitian (ruling out skew-Hermitian `u` via
`Matrix.re_dotProduct_mulVec_eq_zero_of_skewHermitian`), and conjugates by
`TauCeti.rosatiPositiveSquareRoot` of `±u`.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer (2021), §8.4.
* M. Lipnowski and J. Tsimerman, *How large is A_g(F_q)?*, arXiv:1511.02212v1, §4.3.2.
-/

public section

open scoped Matrix ComplexOrder _root_.Quaternion

namespace TauCeti

section SharedNormalization

/-- Transporting `star` on `A` against the canonical star on `M` produces an `F`-algebra
automorphism `X ↦ φ (star (φ.symm (star X)))` of `M`, once scalar compatibility holds. -/
private def transportStarAlgEquiv (F : Type*) {A M : Type*} [Field F] [Ring A] [Algebra ℝ A]
    [StarRing A] [Ring M] [Algebra ℝ M] [Algebra F M] [StarRing M] (φ : A ≃ₐ[ℝ] M)
    (hcomm : ∀ z : F, φ (star (φ.symm (star (algebraMap F M z)))) = algebraMap F M z) :
    M ≃ₐ[F] M :=
  AlgEquiv.ofRingEquiv
    (f := ((starRingEquiv (R := M)).trans φ.symm.toRingEquiv.op).trans
      ((starRingEquiv (R := A)).symm.trans φ.toRingEquiv))
    hcomm

private theorem transportStarAlgEquiv_apply (F : Type*) {A M : Type*} [Field F] [Ring A]
    [Algebra ℝ A] [StarRing A] [Ring M] [Algebra ℝ M] [Algebra F M] [StarRing M] (φ : A ≃ₐ[ℝ] M)
    (hcomm : ∀ z : F, φ (star (φ.symm (star (algebraMap F M z)))) = algebraMap F M z) (X : M) :
    transportStarAlgEquiv F φ hcomm X = φ (star (φ.symm (star X))) := rfl

private theorem compMatrixTrace_conj_pos_of_trace_eq {A D : Type*} [Ring A] [Algebra ℝ A]
    [StarRing A] [Ring D] [Algebra ℝ D] [StarRing D] {n : Type*} [Fintype n] [DecidableEq n]
    {rePart : D →ₗ[ℝ] ℝ} (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
    (ht : ∀ x : A, t x = c * rePart.compMatrixTrace (φ x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) (u : (Matrix n n D)ˣ)
    (hσ : ∀ x : A, φ (star x) = (u : Matrix n n D) * (φ x)ᴴ * (↑u⁻¹ : Matrix n n D))
    (X : Matrix n n D) (hX : X ≠ 0) :
    0 < rePart.compMatrixTrace (X * (u : Matrix n n D) * Xᴴ * (↑u⁻¹ : Matrix n n D)) := by
  have h1 := hpos (φ.symm X) (fun h ↦ hX (by simpa using congrArg φ h))
  rw [ht, map_mul, hσ, AlgEquiv.apply_symm_apply] at h1
  simpa only [mul_assoc] using pos_of_mul_pos_right h1 hc.le

private theorem exists_pos_hermitian_unit {D : Type*} [DivisionRing D] [Algebra ℝ D]
    [StarRing D] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {rePart : D →ₗ[ℝ] ℝ}
    (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (hre_sa : ∀ a : D, IsSelfAdjoint a → a = algebraMap ℝ D (rePart a))
    (u : (Matrix n n D)ˣ) (huH : (u : Matrix n n D)ᴴ = u)
    (hpos : ∀ X : Matrix n n D, X ≠ 0 →
      0 < rePart.compMatrixTrace (X * (u : Matrix n n D) * Xᴴ * (↑u⁻¹ : Matrix n n D))) :
    ∃ a : (Matrix n n D)ˣ, IsRosatiPositive rePart.compMatrixTrace (a : Matrix n n D) ∧
      ∀ X : Matrix n n D, (a : Matrix n n D) * Xᴴ * (↑a⁻¹ : Matrix n n D) =
        (u : Matrix n n D) * Xᴴ * (↑u⁻¹ : Matrix n n D) := by
  have huinvH : (↑u⁻¹ : Matrix n n D)ᴴ = ↑u⁻¹ := IsSelfAdjoint.of_mul_eq_one huH u.mul_inv
  have hre1 : rePart 1 = 1 :=
    ((algebraMap ℝ D).injective (by simpa using hre_sa 1 (IsSelfAdjoint.one D))).symm
  let v₀ : n → D := Pi.single (Classical.arbitrary n) 1
  have hv₀ : v₀ ≠ 0 := fun h ↦ by simpa [v₀] using congrFun h (Classical.arbitrary n)
  set α : ℝ := rePart (star v₀ ⬝ᵥ ((↑u⁻¹ : Matrix n n D) *ᵥ v₀))
  have hprod (w : n → D) (hw : w ≠ 0) : 0 < α * rePart (star w ⬝ᵥ ((u : Matrix n n D) *ᵥ w)) := by
    have h1 := hpos (Matrix.vecMulVec v₀ (star w)) (by simp [hv₀, hw])
    rw [LinearMap.compMatrixTrace_rankOne_mul_conj hre_cyclic _ _ v₀ w] at h1
    have hq1 := hre_sa _ (Matrix.IsHermitian.star_dotProduct_mulVec_comm huinvH v₀ v₀)
    have hq2 := hre_sa _ (Matrix.IsHermitian.star_dotProduct_mulVec_comm huH w w)
    have hmul : rePart ((star v₀ ⬝ᵥ ((↑u⁻¹ : Matrix n n D) *ᵥ v₀)) *
        (star w ⬝ᵥ ((u : Matrix n n D) *ᵥ w))) =
        α * rePart (star w ⬝ᵥ ((u : Matrix n n D) *ᵥ w)) := by
      (conv_lhs => rw [hq1, hq2])
      rw [← map_mul, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, hre1, mul_one]
    rwa [hmul] at h1
  rcases lt_or_gt_of_ne (fun h0 ↦ lt_irrefl 0 (by simpa [h0] using hprod v₀ hv₀) : α ≠ 0) with
      hlt | hgt
  · refine ⟨-u, (isRosatiPositive_compMatrixTrace_iff hre_cyclic _).mpr ⟨by
        rw [Matrix.IsHermitian, Units.val_neg, Matrix.conjTranspose_neg, huH], fun w hw ↦ ?_⟩,
      fun _ ↦ by simp⟩
    have hp := hprod w hw; rw [Units.val_neg, Matrix.neg_mulVec, dotProduct_neg, map_neg]; nlinarith
  · exact ⟨u, (isRosatiPositive_compMatrixTrace_iff hre_cyclic _).mpr
      ⟨huH, fun w hw ↦ pos_of_mul_pos_right (hprod w hw) hgt.le⟩, fun _ ↦ rfl⟩

/-- Conjugating by the internal positive square root `r` of `±u` (`X ↦ r⁻¹ * X * r`) yields a
star-preserving `ℝ`-algebra isomorphism matching `IsRosatiPositive t` with
`IsRosatiPositive rePart.compMatrixTrace`. -/
private theorem exists_star_algEquiv_matrix_of_hermitian_unit {A D : Type*}
    [Ring A] [Algebra ℝ A] [StarRing A] [DivisionRing D] [Algebra ℝ D] [StarRing D]
    [Module.Finite ℝ D] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {rePart : D →ₗ[ℝ] ℝ}
    (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (hre_pos : ∀ a : D, a ≠ 0 → 0 < rePart (a * star a))
    (hre_sa : ∀ a : D, IsSelfAdjoint a → a = algebraMap ℝ D (rePart a))
    (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
    (ht : ∀ x : A, t x = c * rePart.compMatrixTrace (φ x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x))
    (u : (Matrix n n D)ˣ) (huH : (u : Matrix n n D)ᴴ = u)
    (hσ : ∀ x : A, φ (star x) = (u : Matrix n n D) * (φ x)ᴴ * (↑u⁻¹ : Matrix n n D)) :
    ∃ e : A ≃⋆ₐ[ℝ] Matrix n n D,
      ∀ s : A, IsRosatiPositive t s ↔ IsRosatiPositive rePart.compMatrixTrace (e s) := by
  have hMpos := compMatrixTrace_conj_pos_of_trace_eq φ t c hc ht hpos u hσ
  obtain ⟨a, haPos, haConj⟩ := exists_pos_hermitian_unit hre_cyclic hre_sa u huH hMpos
  obtain ⟨_, r, hrPos, hrsq, -, -, -, -⟩ := rosatiPositiveSquareRoot rePart.compMatrixTrace
    (LinearMap.compMatrixTrace_cyclic hre_cyclic)
    (fun _ hX ↦ LinearMap.compMatrixTrace_pos hre_pos hX) (a : Matrix n n D) haPos
  set R := (r : Matrix n n D); set Rinv := (↑r⁻¹ : Matrix n n D)
  have hrH : Rᴴ = R := hrPos.isSelfAdjoint
  have hrInvH : Rinvᴴ = Rinv := IsSelfAdjoint.of_mul_eq_one hrH r.mul_inv
  have haInv : (↑a⁻¹ : Matrix n n D) = Rinv * Rinv := by
    have hmul : (a : Matrix n n D) * (Rinv * Rinv) = 1 := by
      rw [← hrsq, mul_assoc R R, ← mul_assoc R Rinv, r.mul_inv, one_mul, r.mul_inv]
    simpa [mul_assoc] using (congrArg ((↑a⁻¹ : Matrix n n D) * ·) hmul).symm
  let eAlg := φ.trans (MulSemiringAction.toAlgEquiv ℝ _ (ConjAct.toConjAct r⁻¹))
  have he_apply (x : A) : eAlg x = Rinv * φ x * R := by simp [eAlg, ConjAct.units_smul_def, R, Rinv]
  have heStar (x : A) : eAlg (star x) = star (eAlg x) := by
    rw [he_apply (star x), Matrix.star_eq_conjTranspose, he_apply x, hσ, ← haConj, ← hrsq, haInv,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hrH, hrInvH]
    simp only [mul_assoc, R, Rinv, Units.inv_mul_cancel_left, r.inv_mul, mul_one]
  let e : A ≃⋆ₐ[ℝ] Matrix n n D := StarAlgEquiv.ofAlgEquiv eAlg heStar
  have heTrace : t = (c • rePart.compMatrixTrace).comp e.toAlgEquiv.toLinearMap := by
    ext x
    have htr : rePart.compMatrixTrace (e x) = rePart.compMatrixTrace (φ x) := by
      change rePart.compMatrixTrace (eAlg x) = _
      rw [he_apply x, LinearMap.compMatrixTrace_cyclic hre_cyclic (Rinv * φ x) R,
        ← mul_assoc, r.mul_inv, one_mul]
    rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearMap.smul_apply, smul_eq_mul]
    exact (ht x).trans (congrArg (c * ·) htr.symm)
  refine ⟨e, fun s ↦ ?_⟩
  rw [heTrace, isRosatiPositive_iff_of_starAlgEquiv e, isRosatiPositive_iff, isRosatiPositive_iff]
  exact and_congr_right fun _ ↦ forall₂_congr fun X _ ↦
    ⟨fun h ↦ pos_of_mul_pos_right h hc.le, fun h ↦ mul_pos hc h⟩

private theorem exists_pos_const_compMatrixTrace_of_cyclic {A D : Type*} [Ring A] [Algebra ℝ A]
    [StarRing A] [Ring D] [Nontrivial D] [Algebra ℝ D] {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (rePart : D →ₗ[ℝ] ℝ) (hre1 : rePart 1 = 1)
    (hD_cyc : ∀ τ : D →ₗ[ℝ] ℝ, (∀ a b : D, τ (a * b) = τ (b * a)) → ∀ a : D, τ a = τ 1 * rePart a)
    (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : A, t x = c * rePart.compMatrixTrace (φ x) := by
  let tM : Matrix n n D →ₗ[ℝ] ℝ := t.comp φ.symm.toLinearMap
  obtain ⟨τ, hτ_cyc, hτ⟩ := LinearMap.exists_eq_comp_matrixTrace_of_cyclic tM fun X Y ↦ by
    simp only [tM, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, hcyclic]
  have hc : 0 < τ 1 := by
    have h1 : 0 < t 1 := by
      simpa using hpos 1 fun h0 ↦ one_ne_zero (α := Matrix n n D) (by simpa using congrArg φ h0)
    have ht1 : t 1 = τ (Fintype.card n : D) := by simpa [tM, Matrix.trace_one] using hτ 1
    have hcard : (Fintype.card n : D) = (Fintype.card n : ℝ) • (1 : D) := by
      rw [Algebra.smul_def, mul_one, map_natCast]
    rw [ht1, hD_cyc τ hτ_cyc, hcard, map_smul, smul_eq_mul, hre1, mul_one, mul_comm] at h1
    exact pos_of_mul_pos_right h1 (Nat.cast_pos.mpr Fintype.card_pos).le
  refine ⟨τ 1, hc, fun x ↦ ?_⟩
  have h1 : t x = τ (Matrix.trace (φ x)) := by simpa [tM] using hτ (φ x)
  rw [h1, hD_cyc τ hτ_cyc, LinearMap.compMatrixTrace_apply]

private theorem exists_unit_conj_real_central {A D : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    [StarModule ℝ A] [DivisionRing D] [Algebra ℝ D] [StarRing D] [StarModule ℝ D]
    [Algebra.IsCentral ℝ D] [FiniteDimensional ℝ D] {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (φ : A ≃ₐ[ℝ] Matrix n n D) :
    ∃ u : (Matrix n n D)ˣ, ((u : Matrix n n D)ᴴ = u ∨ (u : Matrix n n D)ᴴ = -u) ∧
      ∀ x : A, φ (star x) = (u : Matrix n n D) * (φ x)ᴴ * (↑u⁻¹ : Matrix n n D) := by
  let α := transportStarAlgEquiv ℝ φ fun r ↦ by simp [Algebra.algebraMap_eq_smul_one, star_smul]
  obtain ⟨u, μ, hu, huμ, hμsq⟩ := exists_unit_conj_star_of_central ℝ α fun X ↦ by
    simp only [α, transportStarAlgEquiv_apply, star_star, AlgEquiv.symm_apply_apply,
      AlgEquiv.apply_symm_apply]
  refine ⟨u, ?_, fun x ↦ by
    simpa [α, transportStarAlgEquiv_apply, Matrix.star_eq_conjTranspose] using hu (φ x)ᴴ⟩
  rw [← Matrix.star_eq_conjTranspose]
  rcases mul_self_eq_one_iff.mp (by simpa using hμsq) with rfl | rfl <;>
    [exact Or.inl (by simpa using huμ); exact Or.inr (by simpa using huμ)]

end SharedNormalization

section RealFactor

private theorem not_pos_of_skewSymmetric_real {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (u : (Matrix n n ℝ)ˣ) (hskew : (u : Matrix n n ℝ)ᴴ = -u)
    (hpos : ∀ X : Matrix n n ℝ, X ≠ 0 →
      0 < (LinearMap.id : ℝ →ₗ[ℝ] ℝ).compMatrixTrace
        (X * (u : Matrix n n ℝ) * Xᴴ * (↑u⁻¹ : Matrix n n ℝ))) : False := by
  let v₀ : n → ℝ := Pi.single (Classical.arbitrary n) 1
  have hv₀ : v₀ ≠ 0 := fun h ↦ by simpa [v₀] using congrFun h (Classical.arbitrary n)
  have hposX := hpos (Matrix.vecMulVec v₀ (star v₀)) (by simp [hv₀])
  rw [LinearMap.compMatrixTrace_rankOne_mul_conj (fun a b ↦ mul_comm a b) _ _ v₀ v₀] at hposX
  have hskewQ : star v₀ ⬝ᵥ ((u : Matrix n n ℝ) *ᵥ v₀) = 0 := by
    have hsa := Matrix.star_dotProduct_mulVec_self_of_skewHermitian hskew v₀
    rw [star_trivial] at hsa; linarith
  rw [hskewQ, mul_zero, map_zero] at hposX; exact lt_irrefl 0 hposX

private theorem exists_star_algEquiv_empty {A D : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    [Ring D] [Algebra ℝ D] [StarRing D] {n : Type*} [Fintype n] [DecidableEq n] [IsEmpty n]
    (φ : A ≃ₐ[ℝ] Matrix n n D) (t : A →ₗ[ℝ] ℝ) (P : Matrix n n D → Prop)
    (hP : ∀ X : Matrix n n D, P X) :
    ∃ e : A ≃⋆ₐ[ℝ] Matrix n n D, ∀ s : A, IsRosatiPositive t s ↔ P (e s) :=
  have : Subsingleton A := φ.injective.subsingleton
  ⟨StarAlgEquiv.ofAlgEquiv φ fun _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨fun _ ↦ hP _, fun _ ↦
    isRosatiPositive_iff.mpr ⟨Subsingleton.elim _ _, fun x hx ↦ absurd (Subsingleton.elim x 0) hx⟩⟩⟩

/-- Existence of a star-preserving `ℝ`-algebra isomorphism `e : A ≃⋆ₐ[ℝ] Matrix n n ℝ` identifying
`IsRosatiPositive t` with `Matrix.PosDef`. -/
theorem exists_star_algEquiv_matrix_real {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℝ)
    (t : A →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ e : A ≃⋆ₐ[ℝ] Matrix n n ℝ, ∀ s : A, IsRosatiPositive t s ↔ (e s).PosDef := by
  rcases isEmpty_or_nonempty n with hempty | hne
  · exact exists_star_algEquiv_empty φ t _ fun _ ↦ Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨Subsingleton.elim _ _, fun v hv ↦ absurd (Subsingleton.elim v 0) hv⟩
  · have : StarModule ℝ A := starModule_of_trace_mul_star_pos t hpos
    obtain ⟨c, hc, ht⟩ := exists_pos_const_compMatrixTrace_of_cyclic (LinearMap.id : ℝ →ₗ[ℝ] ℝ) rfl
      (fun τ _ a ↦ by simpa [mul_comm] using τ.map_smul a (1 : ℝ)) φ t hcyclic hpos
    obtain ⟨u, huSign, hσ⟩ := exists_unit_conj_real_central φ
    have huH : (u : Matrix n n ℝ)ᴴ = u := huSign.resolve_right fun hskew ↦
      not_pos_of_skewSymmetric_real u hskew
        (compMatrixTrace_conj_pos_of_trace_eq φ t c hc ht hpos u hσ)
    obtain ⟨e, hePos⟩ := exists_star_algEquiv_matrix_of_hermitian_unit (fun a b ↦ mul_comm a b)
      (fun a ha ↦ by simpa using mul_self_pos.mpr ha) (fun _ _ ↦ rfl) φ t c hc ht hpos u huH hσ
    exact ⟨e, fun s ↦ by simpa using hePos s⟩

end RealFactor

section ComplexFactor

private theorem star_I_smul_one_eq_neg {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (t : A →ₗ[ℝ] ℝ) (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    φ (star (φ.symm (Complex.I • (1 : Matrix n n ℂ)))) = -(Complex.I • (1 : Matrix n n ℂ)) := by
  let M := Matrix n n ℂ; let z : M := Complex.I • (1 : M); let w : M := φ (star (φ.symm z))
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
  have h0 : (c - Complex.I) * (c + Complex.I) = 0 := by linear_combination hc_sq - Complex.I_mul_I
  rcases (mul_eq_zero.mp h0).imp sub_eq_zero.mp eq_neg_of_add_eq_zero_left with rfl | rfl
  · exfalso
    have hz_ne : φ.symm z ≠ 0 := fun h0 ↦ Complex.I_ne_zero <| by
      simpa [z, M] using congrFun (congrFun (congrArg φ h0)
        (Classical.arbitrary n)) (Classical.arbitrary n)
    have h1 := hpos (φ.symm z) hz_ne
    have hstar : φ (star (φ.symm z)) = Complex.I • (1 : M) := by
      simpa [w, Algebra.algebraMap_eq_smul_one] using hc.symm
    have h2 : φ.symm z * star (φ.symm z) = -1 := φ.injective <| by
      rw [map_mul, AlgEquiv.apply_symm_apply, hstar]; simp [z, smul_smul, Complex.I_mul_I]
    have hone : 0 < t 1 :=
      by simpa using hpos 1 fun h0 ↦ one_ne_zero (α := M) (by simpa using congrArg φ h0)
    rw [h2, map_neg] at h1; linarith
  · simpa [w, z, Algebra.algebraMap_eq_smul_one, neg_smul] using hc.symm

private theorem star_scalar_complex {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    [StarModule ℝ A] {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (hI : φ (star (φ.symm (Complex.I • (1 : Matrix n n ℂ)))) = -(Complex.I • (1 : Matrix n n ℂ)))
    (c : ℂ) : φ (star (φ.symm (c • (1 : Matrix n n ℂ)))) = (star c) • (1 : Matrix n n ℂ) := by
  have hsm : c • (1 : Matrix n n ℂ) =
      c.re • (1 : Matrix n n ℂ) + c.im • (Complex.I • (1 : Matrix n n ℂ)) := by
    ext i j; by_cases hij : i = j <;> simp [hij, Complex.real_smul]
  rw [hsm, map_add, map_smul, map_smul, star_add, star_smul, star_smul, star_trivial c.re,
    star_trivial c.im, map_add, map_smul, map_smul, map_one, star_one, map_one, hI, smul_neg]
  ext i j; by_cases hij : i = j <;> simp [hij, Complex.real_smul, Complex.ext_iff]

private theorem exists_hermitian_rescale_complex {n : Type*} [Fintype n] [DecidableEq n]
    (u : (Matrix n n ℂ)ˣ) (μ : ℂ) (huμ : (u : Matrix n n ℂ)ᴴ = μ • (u : Matrix n n ℂ))
    (hμsq : star μ * μ = 1) :
    ∃ u' : (Matrix n n ℂ)ˣ, (u' : Matrix n n ℂ)ᴴ = u' ∧
      ∀ X : Matrix n n ℂ, (u' : Matrix n n ℂ) * X * (↑u'⁻¹ : Matrix n n ℂ) =
        (u : Matrix n n ℂ) * X * (↑u⁻¹ : Matrix n n ℂ) := by
  let ζ : ℂ := if μ = -1 then Complex.I else 1 + μ
  have hζ0 : ζ ≠ 0 := by
    by_cases h : μ = -1
    · simp [ζ, h, Complex.I_ne_zero]
    · simp only [ζ, h, ↓reduceIte]; exact fun h0 ↦ h (eq_neg_of_add_eq_zero_right h0)
  let u' : (Matrix n n ℂ)ˣ := ⟨ζ • (u : Matrix n n ℂ), ζ⁻¹ • (↑u⁻¹ : Matrix n n ℂ),
    by simp [smul_smul, inv_mul_cancel₀ hζ0], by simp [smul_smul, mul_inv_cancel₀ hζ0]⟩
  have hu'val : (u' : Matrix n n ℂ) = ζ • (u : Matrix n n ℂ) := rfl
  have hu'inv : (↑u'⁻¹ : Matrix n n ℂ) = ζ⁻¹ • (↑u⁻¹ : Matrix n n ℂ) := rfl
  refine ⟨u', ?_, fun X ↦ by rw [hu'val, hu'inv]; simp [smul_smul, inv_mul_cancel₀ hζ0]⟩
  rw [hu'val, Matrix.conjTranspose_smul, huμ, smul_smul]; congr 1
  by_cases h : μ = -1
  · simp [ζ, h]
  · simp only [ζ, h, ↓reduceIte, star_add, star_one, add_mul, one_mul]
    rw [add_comm 1 μ]; simpa using congrArg (μ + ·) hμsq

private theorem trace_eq_mul_compMatrixTrace_complex {A : Type*} [Ring A] [Algebra ℝ A]
    [StarRing A] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (hI : φ (star (φ.symm (Complex.I • (1 : Matrix n n ℂ)))) = -(Complex.I • (1 : Matrix n n ℂ)))
    (t' : A →ₗ[ℝ] ℝ) (hcyc' : ∀ x y : A, t' (x * y) = t' (y * x))
    (hstar' : ∀ x : A, t' (star x) = t' x) (hpos' : ∀ x : A, x ≠ 0 → 0 < t' (x * star x)) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : A, t' x = c * Complex.reLm.compMatrixTrace (φ x) := by
  let tM : Matrix n n ℂ →ₗ[ℝ] ℝ := t'.comp φ.symm.toLinearMap
  obtain ⟨τ, -, hτ⟩ := LinearMap.exists_eq_comp_matrixTrace_of_cyclic tM fun X Y ↦ by
    simp only [tM, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, hcyc']
  have hc : 0 < τ 1 := by
    have h1 : 0 < t' 1 :=
      by simpa using hpos' 1 fun h0 ↦ one_ne_zero (α := Matrix n n ℂ) (by simpa using congrArg φ h0)
    have ht1 : t' 1 = τ ((Fintype.card n : ℝ) • (1 : ℂ)) := by
      simpa [tM, Matrix.trace_one, Complex.real_smul] using hτ 1
    rw [ht1, map_smul, smul_eq_mul] at h1
    exact pos_of_mul_pos_right h1 (Nat.cast_nonneg _)
  have hτI : τ Complex.I = 0 := by
    have h1 : tM (Complex.I • (1 : Matrix n n ℂ)) = (Fintype.card n : ℝ) * τ Complex.I := by
      rw [hτ, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, mul_comm,
        ← Complex.ofReal_natCast, ← Complex.real_smul, map_smul, smul_eq_mul]
    have h2 : tM (Complex.I • (1 : Matrix n n ℂ)) = -tM (Complex.I • (1 : Matrix n n ℂ)) := by
      simp only [tM, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]
      conv_lhs => rw [← hstar', ← AlgEquiv.symm_apply_apply φ (star _), hI, map_neg, map_neg]
    exact (mul_eq_zero.mp (by linarith : (Fintype.card n : ℝ) * τ Complex.I = 0)).resolve_left
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine ⟨τ 1, hc, fun x ↦ ?_⟩
  have h1 : t' x = τ ((Matrix.trace (φ x)).re • (1 : ℂ) + (Matrix.trace (φ x)).im • Complex.I) := by
    simpa [tM, Complex.real_smul, Complex.re_add_im] using hτ (φ x)
  rw [h1, map_add, map_smul, map_smul, hτI, smul_zero, add_zero, smul_eq_mul, mul_comm]; rfl

/-- Existence of a star-preserving `ℝ`-algebra isomorphism `e : A ≃⋆ₐ[ℝ] Matrix n n ℂ` identifying
`IsRosatiPositive t` with `Matrix.PosDef`. The proof normalizes the star-symmetrized functional
`t' x = (t x + t (star x)) / 2`, which has the same Rosati-positive cone as `t`. -/
theorem exists_star_algEquiv_matrix_complex {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℂ)
    (t : A →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ e : A ≃⋆ₐ[ℝ] Matrix n n ℂ, ∀ s : A, IsRosatiPositive t s ↔ (e s).PosDef := by
  rcases isEmpty_or_nonempty n with hempty | hne
  · exact exists_star_algEquiv_empty φ t _ fun _ ↦ Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨Subsingleton.elim _ _, fun v hv ↦ absurd (Subsingleton.elim v 0) hv⟩
  · have : StarModule ℝ A := starModule_of_trace_mul_star_pos t hpos
    let t' : A →ₗ[ℝ] ℝ := (t.comp (selfAdjoint.submodule ℝ A).subtype).comp (selfAdjointPart ℝ)
    have hpos' (x : A) (hx : x ≠ 0) : 0 < t' (x * star x) :=
      LinearMap.comp_selfAdjointPart_mul_star_pos hpos hx
    have hI := star_I_smul_one_eq_neg φ t' hpos'
    obtain ⟨c, hc, ht⟩ := trace_eq_mul_compMatrixTrace_complex φ hI t'
      (LinearMap.comp_selfAdjointPart_cyclic hcyclic) t.comp_selfAdjointPart_star hpos'
    let α := transportStarAlgEquiv ℂ φ fun z ↦ by
      simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one, star_scalar_complex φ hI,
        star_star]
    obtain ⟨u, μ, hu, huμ, hμsq⟩ := exists_unit_conj_star_of_central ℂ α fun X ↦ by
      simp [α, transportStarAlgEquiv_apply]
    obtain ⟨u', hu'H, hu'conj⟩ := exists_hermitian_rescale_complex u μ
      (by rw [← Matrix.star_eq_conjTranspose]; exact huμ) hμsq
    have hσ (x : A) : φ (star x) = (u' : Matrix n n ℂ) * (φ x)ᴴ * (↑u'⁻¹ : Matrix n n ℂ) := by
      rw [hu'conj]
      simpa [α, transportStarAlgEquiv_apply, Matrix.star_eq_conjTranspose] using hu (φ x)ᴴ
    obtain ⟨e, hePos⟩ := exists_star_algEquiv_matrix_of_hermitian_unit (rePart := Complex.reLm)
      (fun a b ↦ by rw [mul_comm])
      (fun a ha ↦ by simpa [Complex.normSq_apply] using Complex.normSq_pos.mpr ha)
      (fun a ha ↦ Complex.ext rfl (by
        have := congrArg Complex.im ha; simp only [RCLike.star_def, Complex.conj_im] at this
        simp [show a.im = 0 by linarith]))
      φ t' c hc ht hpos' u' hu'H hσ
    exact ⟨e, fun s ↦ by
      rw [← isRosatiPositive_iff_of_symmetrize t.comp_selfAdjointPart_apply hcyclic, hePos]; simp⟩

end ComplexFactor

section QuaternionFactor

private theorem not_pos_of_skewHermitian_quaternion {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (u : (Matrix n n ℍ[ℝ])ˣ) (hskew : (u : Matrix n n ℍ[ℝ])ᴴ = -u)
    (hpos : ∀ X : Matrix n n ℍ[ℝ], X ≠ 0 →
      0 < (QuaternionAlgebra.reₗ (-1) 0 (-1)).compMatrixTrace
        (X * (u : Matrix n n ℍ[ℝ]) * Xᴴ * (↑u⁻¹ : Matrix n n ℍ[ℝ]))) : False := by
  have hre_cyc (a b : ℍ[ℝ]) : (QuaternionAlgebra.reₗ (-1) 0 (-1)) (a * b) =
      (QuaternionAlgebra.reₗ (-1) 0 (-1)) (b * a) := by
    simp only [QuaternionAlgebra.reₗ_apply, Quaternion.re_mul]; ring
  set Uinv : Matrix n n ℍ[ℝ] := (↑u⁻¹ : Matrix n n ℍ[ℝ])
  have huinv_skew : Uinvᴴ = -Uinv := by
    have h1 := congrArg (· * Uinv) (congrArg Matrix.conjTranspose u.mul_inv)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_one, hskew, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_assoc, u.mul_inv, Matrix.mul_one, Matrix.one_mul] at h1
    exact neg_eq_iff_eq_neg.mp h1
  let i₀ : n := Classical.arbitrary n; let v₀ : n → ℍ[ℝ] := Pi.single i₀ 1
  have hv₀ : v₀ ≠ 0 := fun h ↦ by simpa [v₀] using congrFun h i₀
  set r : ℍ[ℝ] := star v₀ ⬝ᵥ (Uinv *ᵥ v₀); set s : ℍ[ℝ] := star v₀ ⬝ᵥ ((u : Matrix n n ℍ[ℝ]) *ᵥ v₀)
  have hpos0 : 0 < (r * s).re := by
    have h := hpos (Matrix.vecMulVec v₀ (star v₀)) (by simp [hv₀])
    rwa [LinearMap.compMatrixTrace_rankOne_mul_conj hre_cyc _ Uinv v₀ v₀] at h
  obtain ⟨q, hq0, hqconj⟩ := Quaternion.exists_pure_neg_conj r
    (Matrix.re_dotProduct_mulVec_eq_zero_of_skewHermitian huinv_skew v₀)
  let v₁ : n → ℍ[ℝ] := fun i ↦ v₀ i * q
  have hv₁ : v₁ ≠ 0 := fun h ↦ by have := congrFun h i₀; simp [v₁, v₀, hq0] at this
  have hpos1 : 0 < (-(Quaternion.normSq q • r) * s).re := by
    have h := hpos (Matrix.vecMulVec v₁ (star v₀)) (by simp [hv₁, hv₀])
    rw [LinearMap.compMatrixTrace_rankOne_mul_conj hre_cyc _ Uinv v₁ v₀] at h
    have hQ1 : star v₁ ⬝ᵥ (Uinv *ᵥ v₁) = star q * r * q := by
      simp only [dotProduct, Matrix.mulVec, v₁, r, Pi.star_apply, star_mul, Finset.mul_sum,
        Finset.sum_mul, mul_assoc]
    rwa [hQ1, hqconj] at h
  have hnq : 0 < Quaternion.normSq q := lt_of_not_ge fun h ↦ hq0 (Quaternion.normSq_le_zero.mp h)
  simp only [neg_mul, QuaternionAlgebra.re_neg, smul_mul_assoc, QuaternionAlgebra.re_smul,
    smul_eq_mul] at hpos1
  nlinarith

/-- Existence of a star-preserving `ℝ`-algebra isomorphism `e : A ≃⋆ₐ[ℝ] Matrix n n ℍ[ℝ]`
identifying `IsRosatiPositive t` with `Matrix.QuatPosDef`. -/
theorem exists_star_algEquiv_matrix_quaternion {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : A ≃ₐ[ℝ] Matrix n n ℍ[ℝ])
    (t : A →ₗ[ℝ] ℝ) (hcyclic : ∀ x y : A, t (x * y) = t (y * x))
    (hpos : ∀ x : A, x ≠ 0 → 0 < t (x * star x)) :
    ∃ e : A ≃⋆ₐ[ℝ] Matrix n n ℍ[ℝ], ∀ s : A, IsRosatiPositive t s ↔ (e s).QuatPosDef := by
  rcases isEmpty_or_nonempty n with hempty | hne
  · exact exists_star_algEquiv_empty φ t Matrix.QuatPosDef fun X ↦ Matrix.QuatPosDef.of_isEmpty X
  · have : StarModule ℝ A := starModule_of_trace_mul_star_pos t hpos
    let reH : ℍ[ℝ] →ₗ[ℝ] ℝ := QuaternionAlgebra.reₗ (-1) 0 (-1)
    have hre_cyc (a b : ℍ[ℝ]) : reH (a * b) = reH (b * a) := by
      simp only [reH, QuaternionAlgebra.reₗ_apply, Quaternion.re_mul]; ring
    obtain ⟨c, hc, ht⟩ := exists_pos_const_compMatrixTrace_of_cyclic reH rfl
      Quaternion.cyclic_eq_mul_re φ t hcyclic hpos
    obtain ⟨u, huSign, hσ⟩ := exists_unit_conj_real_central φ
    have huH : (u : Matrix n n ℍ[ℝ])ᴴ = u := huSign.resolve_right fun hskew ↦
      not_pos_of_skewHermitian_quaternion u hskew
        (compMatrixTrace_conj_pos_of_trace_eq φ t c hc ht hpos u hσ)
    obtain ⟨e, hePos⟩ := exists_star_algEquiv_matrix_of_hermitian_unit hre_cyc
      (fun _ ha ↦ Quaternion.re_mul_star_pos ha) (fun _ ha ↦ Quaternion.star_eq_self.mp ha)
      φ t c hc ht hpos u huH hσ
    exact ⟨e, fun s ↦ by simpa [reH] using hePos s⟩

end QuaternionFactor

end TauCeti
